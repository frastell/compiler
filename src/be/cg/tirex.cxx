/*
  Copyright (C) 2000, 2001 Silicon Graphics, Inc.  All Rights Reserved.
  Copyright (C) 2011 Kalray SA. All Rights Reserved.
  Copyright (C) 2011 Fabrice Rastello (INRIA, Colorado State University). All Right Reserved.

  This program is free software; you can redistribute it and/or modify it
  under the terms of version 2 of the GNU General Public License as
  published by the Free Software Foundation.

  This program is distributed in the hope that it would be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  

  Further, this software is distributed without any warranty that it is
  free of the rightful claim of any third person regarding infringement 
  or the like.  Any license provided herein, whether implied or 
  otherwise, applies only to this software file.  Patent licenses, if 
  any, provided herein do not apply to combinations of this program with 
  other software, or any other product whatsoever.  

  You should have received a copy of the GNU General Public License along
  with this program; if not, write the Free Software Foundation, Inc., 59
  Temple Place - Suite 330, Boston MA 02111-1307, USA.
 */

#include <assert.h>
#include <iostream>
#include <sstream>
#include <stdio.h>
#include <vector>
#include <queue>
#include <stack>
#include <list>
#include <map>

#include "bb.h"
#include "cg.h"
#include "cgdwarf.h"
#include "cgtarget.h"
#include "cg_dep_graph.h"
#include "cg_flags.h"
#include "cg_loop.h"
#include "const.h"
#include "data_layout.h"
#include "dep_graph.h"
#include "dominate.h"
#include "findloops.h"
#include "glob.h"
#include "op.h"
#include "opt_alias_interface.h"
#include "opt_points_to.h"
#include "sections.h"
#include "stblock.h"
#include "symtab.h"
#include "targ_const_private.h"
#include "whirl2ops.h"
#include "wn.h"

#include "tirex.h"

static char indent[1024];
static int indent_depth = 0;

static void
indent_inc(int spaces)
{
  indent_depth += spaces;
  assert(indent_depth < sizeof(indent));
  memset(indent, ' ', indent_depth);
  indent[indent_depth] = '\0';
}

static void
indent_dec(int spaces)
{
  indent_depth -= spaces;
  assert(indent_depth >= 0);
  memset(indent, ' ', indent_depth);
  indent[indent_depth] = '\0';
}

const char *sep;
static FILE *file;
static int stage = 0;
static ST *text_base = NULL;
static ST *current_section = NULL;

#ifndef TARG_ST
#define OP_Is_Barrier(op)     CGTARG_Is_OP_Barrier(op)
#define ISA_RELOC             mUINT8
#define ISA_RELOC_UNDEFINED   TN_RELOC_NONE
#define Same_Byte_Sex         (Host_Is_Little_Endian == Target_Is_Little_Endian)
#define TOP_ShortName(opcode) TOP_Name(opcode)
#else// TARG_ST
#define ISA_PRINT_Operand_Is_Part_Of_Name(op,i) false
#define Target_Is_Little_Endian (Target_Byte_Sex != BIG_ENDIAN)
#endif

////////////////////////////////////////////////////////////////////////
// Loop forest code


#define LOOPDEBUG 0
BBSSTATE * loopforest_state;

/* Helper function for tirex_build_loopforest
   each node gets preidx & postidx number (used for ancestor checking)
   traversed flag is used to avoid a node to be considered twice
   if t a loop-header, t.BE = { s | (s,t) back-edge) }
   otherwise         , t.P = { s | (s,t) CFG-edge not back-edge }
      t as target, s as source
   reverse_stack is a list of loop headers in DFS post-order (inner to outer most loop)
*/
static void 
tirex_dfs_mark(BB *s_BB, unsigned int *dfsidx, BBSSTATE *state, std::queue<BB_NUM> *reverse_stack)
{
  (*dfsidx)++;
  BB_NUM sidx = BB_id(s_BB);
  BBSSTATE *s = state+sidx;
  BBLIST *item;
  s->preidx = *dfsidx;
  s->isancestor = true;
  s->traversed = true;
  if (LOOPDEBUG) fprintf(stdout, "LOOPDFS %d (predfs=%d)\n", sidx, *dfsidx);
  FOR_ALL_BB_SUCCS(s_BB, item) {
    BB *t_BB = BBLIST_item(item);
    BB_NUM tidx = BB_id(t_BB);
    BBSSTATE *t = state+tidx;
    if (tidx == sidx) {                   // (s,t) self-loop
      s->isloopheader = true;
      t->innermost = true;
      if (LOOPDEBUG) fprintf(stdout, "LOOPSELF %d\n", sidx);
    } else if (t->traversed) {
      if (t->isancestor) {               // (s,t) strict back-edge
	(t->BE).push (sidx);
	t->isloopheader = true;
	t->innermost = true;
	if (LOOPDEBUG) fprintf(stdout, "LOOPHEADER: %d->%d %d->BE+=%d, (%d)\n", sidx, tidx, tidx, sidx, (int) (t->BE).size());
      } else {                            // (s, t) cross/forward-edge
	t->P.push (sidx);
	if (LOOPDEBUG) fprintf(stdout, "LOOPFORWARD: %d->%d  %d->P+=%d, (%d)\n", sidx, tidx, tidx, sidx, (int) (t->P).size());
      }
    } else {                             // (s,t) tree-edge
      t->P.push (sidx);
      if (LOOPDEBUG) fprintf(stdout, "LOOPTREE: %d->%d %d->P+=%d, (%d)\n", sidx, tidx, tidx, sidx, (int) (t->P).size());
      t->entry_bb = s->entry_bb;
      tirex_dfs_mark(t_BB, dfsidx, state, reverse_stack);
    }
  }
  s->postidx = *dfsidx;
  s->isancestor = false;
  if (s->isloopheader) {
    reverse_stack->push(sidx);
    if (LOOPDEBUG) fprintf(stdout, "LOOP stacking (%d)\n", (int) reverse_stack->size());
  }
}

/* Helper function for tirex_build_loopforest
   classical union find.
*/
static BB_NUM 
tirex_LP_find (BBSSTATE *state, BB_NUM hidx) {
  BBSSTATE *h = state+hidx;
  if (h->LP_parent == hidx) return hidx;
  else {
    h->LP_parent = tirex_LP_find(state, h->LP_parent);
    return h->LP_parent;
  }
}
static BB_NUM 
tirex_LP_union (BBSSTATE *state, BB_NUM ridx, BB_NUM nidx) {
  BB_NUM n_Root_idx = tirex_LP_find (state, nidx);
  BBSSTATE *n_Root = state+n_Root_idx;
  BB_NUM r_Root_idx = tirex_LP_find (state, ridx);
  n_Root->LP_parent = r_Root_idx;
}

static void 
tirex_dfs_build_loopchildren(BB *s_BB, BBSSTATE *state) 
{
  /* We do a post order traversal of the DAG */
  BB_NUM sidx = BB_id(s_BB);
  BBSSTATE *s = state+sidx;
  BBLIST *item;

  s->traversed = true;
  FOR_ALL_BB_SUCCS(s_BB, item) {
    BB *t_BB = BBLIST_item(item);
    BB_NUM tidx = BB_id(t_BB);
    BBSSTATE *t = state+tidx;
    if (t->traversed) 
      continue;
    tirex_dfs_build_loopchildren(t_BB, state); 
  }

  BB *h_BB = s->loophead_bb;
  if (h_BB) {
    BB_NUM hidx = BB_id(h_BB);
    BBSSTATE *h = state+hidx;
    (h->loopchildren).push_front(sidx);
    if (LOOPDEBUG) fprintf(stdout, "CHILD %d -> %d\n", hidx, sidx);
  } else {
    BB *e_BB = s-> entry_bb;
    BB_NUM eidx = BB_id(e_BB);
    BBSSTATE *e = state+eidx;
    (e->loopchildren).push_front(sidx);
    if (LOOPDEBUG) fprintf(stdout, "CHILD %d -> %d\n", eidx, sidx);
  }
}

static void
tirex_dfs_build_looplevel(BB *h_BB, BBSSTATE *state, int *depth, int *idx)
{
  /* We do a dfs of the loop nesting forest */
  BB_NUM hidx = BB_id(h_BB);
  BBSSTATE *h = state+hidx;
  if (h->isloopheader) {
    (*depth)++;
    (*idx)++;
    h->loopidx = *idx;
  }
  h->loopdepth = *depth;
  std::list<BB_NUM>::iterator child;
  for (child = (h->loopchildren).begin(); child!= (h->loopchildren).end(); ++child) {
    BB_NUM cidx = *child;
    BB *c_BB = BB_Vec[cidx];
    if (cidx != hidx) tirex_dfs_build_looplevel(c_BB, state, depth, idx);
  }
  if (h->isloopheader) (*depth)--;
}


/*  Builds the loop forest for the PU.
    After the algorithm:
     - each bb as a x_loophead_bb which is the bb of its parent in the 
       loop forest (if exists)
        
    loops are processed from inner to outer
    classical union find (LP_find, LP_union) to find the outermost processed loop
    a worklist to enumerate every loop headers (outermost inner loops) of the loopBody of the current loop. 
    any element of worklist is a descendant of h to be appended (if not already, which can be easily checked using LP_find) to the loopBody of h. 
*/
BBSSTATE *
tirex_build_loopforest()
{
  BBSSTATE *state = new BBSSTATE[PU_BB_Count+1];
  std::queue<BB_NUM> reverse_stack;
  BB_NUM i;
  BB_LIST *entl;
  unsigned int dfsidx;
  for (i=1; i<=PU_BB_Count;i++) {
    BBSSTATE *s = state+i;
    s->LP_parent = i;
    s->isloopheader = false;
    s->innermost = false;
    s->irreducible = false;
    s->isancestor = false;
    s->traversed = false;
    s->loophead_bb = NULL;
    s->loopidx = 0;
    s->entry_bb = NULL;
  }
  { 
    state->isloopheader = false;
  }
  dfsidx = 0;
  for (entl = Entry_BB_Head; entl; entl = BB_LIST_rest(entl)) {
    BB *entry_BB = BB_LIST_first(entl);
    BB_NUM eidx = BB_id(entry_BB);
    BBSSTATE *e = state+eidx;
    if (!(e->entry_bb)) {
      e->entry_bb = entry_BB;
      tirex_dfs_mark (entry_BB, &dfsidx, state, &reverse_stack); 
    }
  }
  while (!reverse_stack.empty()) {
    BB_NUM hidx = reverse_stack.front();
    std::stack<BB_NUM> worklist;
    BBSSTATE *h = state+hidx;
    reverse_stack.pop();
    if (LOOPDEBUG) fprintf(stdout, "LOOP unstack %d\n", hidx);
    while (!(h->BE).empty()) {
      BB_NUM nidx = (h->BE).top();
      (h->BE).pop();
      worklist.push(tirex_LP_find(state, nidx));
    }
    while (!worklist.empty()) {
      BB_NUM tidx = worklist.top();
      BBSSTATE *t = state+tidx;
      worklist.pop();
      if (tirex_LP_find(state, tidx) == hidx)
	continue;            // can be several times in the worklist
      tirex_LP_union(state, hidx, tidx);
      if (LOOPDEBUG) fprintf(stdout, "LOOP %d -> %d\n", tidx, hidx);
      t->loophead_bb = BB_Vec[hidx];
      if (t->isloopheader) h->innermost = false;
      while (!(t->P).empty()) {
	BB_NUM sidx = (t->P).top();
	BB_NUM midx = tirex_LP_find(state, sidx);
	BBSSTATE *m = state+midx;
	(t->P).pop();
	if (LOOPDEBUG) fprintf(stdout, "LOOPchildren %d=find(%d)\n", midx, sidx);
	if ((h->preidx < m->preidx) && (m->preidx <= h->postidx)) // h strict ancestor of m
	  worklist.push(midx);
	else if (hidx != midx) { // postpone the processing of (s,t) (replace by (s,h))
	  (h->P).push(sidx);
	  h->irreducible = true;
	}
      }
    }
  }  
  /* Now we have computed the loopheader for each BB, we compute the loop-children
     for each loop header, ordered in topological order of the DAG */
  for (i=1; i<=PU_BB_Count;i++) {
    BBSSTATE *s = state+i;
    s->traversed = false;
  }
  for (entl = Entry_BB_Head; entl; entl = BB_LIST_rest(entl)) {
    BB *entry_BB = BB_LIST_first(entl);
    tirex_dfs_build_loopchildren(entry_BB, state);
  }
  for (entl = Entry_BB_Head; entl; entl = BB_LIST_rest(entl)) {
    BB *entry_BB = BB_LIST_first(entl);
    int depth = 0; // for loop depth
    int idx = 0; // for loopidx
    tirex_dfs_build_looplevel(entry_BB, state, &depth, &idx);
  }
  return state;
}

/* If called as follow:
  for (entl = Entry_BB_Head; entl; entl = BB_LIST_rest(entl)) {
    BB *entry_BB = BB_LIST_first(entl);
    BB_NUM eidx = BB_id(entry_BB);
    tirex_loopbody(state, &loopbody, eidx)
  }
  loopbody is a list of all BB of the PU ordered in topological order

  If called as follow with header_BB a loop header:
  {
    BB_NUM hidx = BB_idx(header_BB);
    tirex_loopbody(state, &loopbody, hidx)
  }  
  loopbody is a list of all BB of the loop of header header_BB
*/
void tirex_loopbody(BBSSTATE *state, std::list<BB*> *loopbody, BB_NUM hidx)
{
  BBSSTATE *h = state+hidx;
  bool firstcall = loopbody->empty();
  loopbody->push_back(BB_Vec[hidx]);
  if (LOOPDEBUG) {
    if (firstcall)
      fprintf(stdout, "LOOPBODY (%d): ", hidx);
    fprintf(stdout, "%d ", hidx);
  }
  std::list<BB_NUM>::iterator child;
  for (child = (h->loopchildren).begin(); child!= (h->loopchildren).end(); ++child) {
    BB_NUM cidx = *child;
    if (cidx != hidx) tirex_loopbody(state, loopbody, cidx);
  }
  if (LOOPDEBUG && firstcall) fprintf(stdout, "\n");
}

/* If called as follow:
  for (entl = Entry_BB_Head; entl; entl = BB_LIST_rest(entl)) {
    BB *entry_BB = BB_LIST_first(entl);
    BB_NUM eidx = BB_id(entry_BB);
    tirex_loopupperbody(state, &loopbody, eidx)
  }
  loopbody is a list of all BB not part of any loop of the PU ordered 
    in topological order

  If called as follow with header_BB a loop header:
  {
    BB_NUM hidx = BB_idx(header_BB);
    tirex_loopupperbody(state, &loopbody, hidx)
  }  
  loopbody is a list of all BB not part of any inner loop of the loop of 
    header header_BB
*/
void tirex_loopupperbody(BBSSTATE *state, std::list<BB*> *loopbody, BB_NUM hidx)
{
  BBSSTATE *h = state+hidx;
  if (LOOPDEBUG) fprintf(stdout, "LOOPUPPERBODY (%d): ", hidx);
  if (hidx==0) {
    for (BB_LIST *entl = Entry_BB_Head; entl; entl = BB_LIST_rest(entl)) {
      BB *entry_BB = BB_LIST_first(entl);
      BB_NUM eidx = BB_id(entry_BB);
      tirex_loopupperbody(loopforest_state, loopbody, eidx);
    }
  } else {
    if (h->isloopheader) {
      loopbody->push_back(BB_Vec[hidx]);
      if (LOOPDEBUG) fprintf(stdout, "%d ", hidx);
    }
    for (std::list<BB_NUM>::iterator child = (h->loopchildren).begin(); child!= (h->loopchildren).end(); ++child) {
      BB_NUM bbidx = *child;
      BBSSTATE *bb = state + bbidx;
      if (!(bb->isloopheader)) {
	loopbody->push_back(BB_Vec[bbidx]);
	if (LOOPDEBUG) fprintf(stdout, "%d ", bbidx);
      }
    }
    if (LOOPDEBUG) fprintf(stdout, "\n");
  }
}

int 
tirex_dump_loopupperbody(BBSSTATE *state, BB_NUM hidx)
{
  BBSSTATE *h = state+hidx;
  int num=0;
  if (LOOPDEBUG) fprintf(stdout, "LOOPUPPERBODY (%d): ", hidx);
  if (hidx==0) {
    for (BB_LIST *entl = Entry_BB_Head; entl; entl = BB_LIST_rest(entl)) {
      BB *entry_BB = BB_LIST_first(entl);
      BB_NUM eidx = BB_id(entry_BB);
      num += tirex_dump_loopupperbody(loopforest_state, eidx);
    }
  } else {
    sep = "";
    if (h->isloopheader) {
      fprintf(file, "%sB%u", sep, hidx);
      sep = ", ";
    }
    for (std::list<BB_NUM>::iterator child = (h->loopchildren).begin(); child!= (h->loopchildren).end(); ++child) {
      BB_NUM bbidx = *child;
      BBSSTATE *bb = state + bbidx;
      if (!(bb->isloopheader)) {
        fprintf(file, "%sB%u", sep, bbidx);
        sep = ", ";
      } else {
        fprintf(file, "%s[L%u]", sep, bb->loopidx);
        sep = ", ";
      }
      num++;
    }
  }
  return num;
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Emit TIREX code.

typedef std::list<WN*> WN_List;
typedef std::list<BB*> BB_List;
typedef std::list<OP*> OP_List;
static std::map<RID *, int> region_seen;

static OP_MAP OP_to_NID;
static uint32_t NID;

static uint32_t
OP_node_id(OP *op)
{
  uint32_t node_id = 0;
  if (OP_memory(op) || OP_Is_Barrier(op)) {
    WN *wn = Get_WN_From_Memory_OP(op);
    if (wn) {
      node_id = OP_MAP32_Get(OP_to_NID, op);
      if (node_id == 0) {
        node_id = ++NID;
        OP_MAP32_Set(OP_to_NID, op, node_id);
      }
    }
  }
  return node_id;
}

static BB_MAP BB_to_LID;
static uint32_t LID;

// Test if a BB belongs to a BB_List.
static bool
BB_List_contains(BB_List& bb_list, BB *bb)
{
  //
  BB_List::iterator bb_iter = bb_list.begin();
  for (; bb_iter != bb_list.end(); bb_iter++) {
    if (*bb_iter == bb) return true;
  }
  //
  return false;
}

// Topological sort of a BB_SET into a BB_List
static void
bb_set_topsort_dfs(BB_SET *bb_set, BB *bb, BB_MAP visited_map, BB_List *bb_list)
{
  BB_MAP32_Set(visited_map, bb, 1);
  BBLIST *succs;
  FOR_ALL_BB_SUCCS(bb, succs) {
    BB *succ_bb = BBLIST_item(succs);
    if (!BB_MAP32_Get(visited_map, succ_bb) && BB_SET_MemberP(bb_set, succ_bb)) {
      bb_set_topsort_dfs(bb_set, succ_bb, visited_map, bb_list);
    }
  }
  bb_list->push_front(bb);
}

static void
bb_set_topsort(BB_SET *bb_set, BB *bb, BB_List *bb_list)
{
  BB_MAP visited_map = BB_MAP32_Create();
  bb_set_topsort_dfs(bb_set, bb, visited_map, bb_list);
  BB_MAP_Delete(visited_map);
}

static OP_MAP OP_to_OID;
static uint32_t OID;

static uint32_t
OP_id(OP *op)
{
  uint32_t op_id = OP_MAP32_Get(OP_to_OID, op);
  if (!op_id) {
    op_id = ++OID;
    OP_MAP32_Set(OP_to_OID, op, op_id);
  }
  return op_id;
}

static bool
OP_memorysafe (OP *op)
{
  WN *wn;
  TN *base;
  if (!OP_memory (op)) return FALSE;
#ifdef TARG_ST
  if (OP_Can_Be_Speculative (op)) return TRUE;
#endif
  if (OP_store (op)) {
    if (   (base = OP_Base(op))
        && TN_is_symbol(base)
        && ! ST_is_weak_symbol(TN_var(base))) return TRUE;
    if (   (wn = Get_WN_From_Memory_OP(op))
        && Alias_Manager
        && Safe_to_speculate(Alias_Manager, wn)) return TRUE;
  }
  return FALSE;
}

// See be/cg/cgemit.cxx:EMT_Write_Qualified_Name
static void
tirex_write_name(ST *sym)
{
  if (ST_class(sym) == CLASS_CONST) {
      fprintf(file, "'.LC%u'", (unsigned)ST_IDX_index(ST_st_idx(sym)));
  } else if (ST_name(sym) && *(ST_name(sym)) != '\0') {
    if (ST_is_export_local(sym) && ST_class(sym) == CLASS_VAR) {
      if (ST_level(sym) == GLOBAL_SYMTAB) {
        fprintf (file, "'%s.%u'", ST_name(sym), ST_index(sym));
      } else {
        fprintf (file, "'%s.%u.%u'", ST_name(sym), ST_pu(Get_Current_PU_ST()), ST_index(sym));
      }
    } else {
      fprintf (file, "'%s'", ST_name(sym));
    }
  } else {
    //fprintf (file, "['%s', %+lld]", ST_name(ST_base(sym)), (long long)ST_ofst(sym));
    fprintf (file, "ERROR['%s', %+lld]", ST_name(ST_base(sym)), (long long)ST_ofst(sym));
  }
}

// TIREX for a TN.
void
tirex_emit_tn(TN *tn)
{
  if (TN_is_register(tn)){
    REGISTER reg = TN_register(tn);
    ISA_REGISTER_CLASS irc = TN_register_class(tn);
    if (TN_is_dedicated(tn)) {
      CLASS_REG_PAIR crp = TN_class_reg(tn);
      // On the open64 side, the dedicated property can be set to a temporary register not
      // in the initial dedicated set. And additional information such as home location
      // may be set on such dedicated registers.
      // On the LAO side, dedicated temporaries are shared, so we create dedicated temporaries
      // only if the tn is in the initial dedicated set. Otherwise we create an
      // assigned temporary and set the dedicated flag.
      if (Build_Dedicated_TN(CLASS_REG_PAIR_rclass(crp), CLASS_REG_PAIR_reg(crp), 0) == tn) {
        // Dedicated.
        fprintf(file, "'%s'", REGISTER_name(irc, reg));
      } else {
#if 1
        // Assigned and Dedicated, emit same as Dedicated
        fprintf(file, "'%s'", REGISTER_name(irc, reg));
#else
        // Assigned and Dedicated, emit same as Assigned.
        fprintf(file, "'T%u.%s'", (unsigned)TN_number(tn), REGISTER_name(irc, reg));
#endif
      }
    } else if (TN_register(tn) != REGISTER_UNDEFINED) {
      // Assigned.
      fprintf(file, "'T%u.%s'", (unsigned)TN_number(tn), REGISTER_name(irc, reg));
    } else {
      // Virtual.
      fprintf(file, "T%u", (unsigned)TN_number(tn));
    }
  } else {
    if (TN_has_value(tn)) {
      fprintf(file, "%lld", (long long)TN_value(tn));
    } else
    if (TN_is_tag(tn)) {
      fprintf(file, "'%s'", LABEL_name(TN_label(tn)));
    } else
    if (TN_is_label(tn)) {
      const char *name = LABEL_name(TN_label(tn));
      int64_t offset = TN_offset(tn);
      FmtAssert(offset == 0, ("Label tn with non-zero offset"));
      fprintf(file, "'%s'", name);
    } else
    if (TN_is_symbol(tn)) {
      ST *st = TN_var(tn);
      int64_t offset = TN_offset(tn);
#if 0
      const char *name = ST_name(st);
      if (stage == 1 && Base_Offset_Is_Known(st)) {
        ST **_st = NULL;
        Base_Symbol_And_Offset(st, _st, &offset);
        static char decimal[64];
        sprintf(decimal, "%lld", (long long)offset);
        name = decimal;
        offset = 0;
      }
#endif
      fprintf(file, "[");
      tirex_write_name(st);
      if (offset != 0) {
        fprintf(file, ", %+lld", (long long)offset);
      }
#ifdef TARG_ST // relocation not available in targinfo path64 and available in MDS
      ISA_RELOC reloc = TN_relocs(tn);
      if (reloc != ISA_RELOC_UNDEFINED) {
        const char *name = TN_RELOCS_Name(reloc);
        const char *shortName = strchr(name, '_');
        if (shortName) {
          name = shortName + 1;
        }
        if (*name) {
          if (offset == 0) {
            fprintf(file, ", 0");
          }
          fprintf(file, ", '%s'", name);
        }
      }
#endif
      fprintf(file, "]");
    } else
    if (TN_is_enum(tn)) {
      fprintf(file, "'%s'", ISA_ECV_Name(TN_enum(tn)));
      //fprintf(file, "%d", ISA_ECV_Intval(TN_enum(tn)));
    } else
      FmtAssert(FALSE, ("Unknown tn type"));
  }
}

// TIREX for an OP.
void
tirex_emit_op(OP *op)
{
  fprintf(file, "%s- { ", indent);
  fprintf(file, "op: %s", TOP_ShortName(OP_code(op)));
  //
  // Results.
  if (OP_results(op) > 0) {
    fprintf(file, ", defs: [");
    sep = "";
    for (int i = 0; i < OP_results(op); i++) {
      TN *tn = OP_result(op, i);
      if (TN_is_enum(tn) && ISA_PRINT_Operand_Is_Part_Of_Name(OP_code(op),i))
	continue;
      fprintf(file, "%s", sep);
      tirex_emit_tn(OP_result(op, i));
      sep = ", ";
    }
    fprintf(file, "]"); 
  }
  //
  // Arguments.
  if (OP_opnds(op) > 0) {
    fprintf(file, ", uses: [");
    sep = "";
    for (int i = 0; i < OP_opnds(op); i++) {
      fprintf(file, "%s", sep);
      tirex_emit_tn(OP_opnd(op, i));
      sep = ", ";
    }
    fprintf(file, "]");
  }
  //
  // Clobbers.
  if (OP_call(op) || (OP_code(op) == TOP_asm)) {
    int clobber_count = 0;
    TN *clobbers[ISA_REGISTER_CLASS_COUNT*ISA_REGISTER_MAX];
    ISA_REGISTER_CLASS irc;
    FOR_ALL_ISA_REGISTER_CLASS(irc) {
      REGISTER_SET regset;
      if (OP_call(op)) {
        BB *bb = OP_bb(op);
        regset = BB_call_clobbered(bb, irc);
      } else {
        ASM_OP_ANNOT* asm_info = (ASM_OP_ANNOT*) OP_MAP_Get(OP_Asm_Map, op);
        regset = ASM_OP_clobber_set(asm_info)[irc];
      }
      for (REGISTER reg = REGISTER_SET_Choose(regset);
           reg != REGISTER_UNDEFINED;
           reg = REGISTER_SET_Choose_Next(regset, reg)) {
        TN* tn = Build_Dedicated_TN(irc, reg, 0);
        clobbers[clobber_count++] = tn;
      }
    }
    if (clobber_count) {
      bool range = false;
      REGISTER prev_reg = TN_register(clobbers[0]);
      ISA_REGISTER_CLASS prev_class = TN_register_class(clobbers[0]);
      const char *prev_name = REGISTER_name(prev_class, prev_reg);
      fprintf(file, ", clobbers: [ '%s", prev_name);
      for (int i = 1; i < clobber_count; i++) {
        TN *tn = clobbers[i];
        REGISTER curr_reg = TN_register(tn);
        ISA_REGISTER_CLASS curr_class = TN_register_class(tn);
        const char *curr_name = REGISTER_name(curr_class, curr_reg);
        if (curr_reg == prev_reg + 1 && curr_class == prev_class) {
          range = true;
        } else {
          if (range) {
            fprintf(file, "-%s", prev_name);
          }
          fprintf(file, "', '%s", curr_name);
          range = false;
        }
        prev_name = curr_name;
        prev_class = curr_class;
        prev_reg = curr_reg;
      }
      if (range) {
        fprintf(file, "-%s", prev_name);
      }
      fprintf(file, "' ]");
    }
  }
  // Flags.
  int flags = false;
  sep = "";
  if (OP_copy(op)) {
    if (!flags++) fprintf(file, ", flags: [");
    fprintf(file, "%sPureCopy", sep);
    sep = ", ";
  }
  if (OP_memorysafe(op)) {
    if (!flags++) fprintf(file, ", flags: [");
    fprintf(file, "%sMemorySafe", sep);
    sep = ", ";
  }
  if (OP_hoisted(op)) {
    if (!flags++) fprintf(file, ", flags: [");
    fprintf(file, "%sHoisted", sep);
    sep = ", ";
  }
  if (OP_volatile(op)) {
    if (!flags++) fprintf(file, ", flags: [");
    fprintf(file, "%sVolatile", sep);
    sep = ", ";
  }
  if (flags) fprintf(file, "]");
  // Iteration.
  int instance = OP_unrolling(op);
  if (instance > 0) {
    fprintf(file, ", instance: %d", instance);
  }
  // Dependence Node.
  uint32_t node_id = OP_node_id(op);
  if (node_id) {
    fprintf(file, ", node: N%u", node_id);
    if (0 && Alias_Manager) {
      WN *wn = Get_WN_From_Memory_OP(op);
      char buf[512];
      buf[0]='\0';
      Print_alias_info(buf, Alias_Manager, wn);
      fprintf(file, ", alias: '%s'", buf);
    }
  }
  //
  fprintf(file, " }\n");
  // if (node_id && Alias_Manager) {
    // WN *wn = Get_WN_From_Memory_OP(op);
    // fprintf(file, "ALIAS: ");
    // Dump_alias_mgr(Alias_Manager, wn, file);
  // }
}

void
tirex_emit_loopdesc(BB *bb) {
  BB_NUM hidx = BB_id(bb);
  BBSSTATE *h = loopforest_state + hidx;
  ANNOTATION *annot_remainder = NULL;
  fprintf(file, "%sdepth: %d\n", indent, h->loopdepth);
  if (h->loophead_bb) fprintf(file, "%sparent: L%u\n", indent, h->loopidx);
  LOOP_DESCR *loop = BB_loophead(bb) ? LOOP_DESCR_Find_Loop(bb) : NULL;
  LOOPINFO *loopinfo = loop ? LOOP_DESCR_loopinfo(loop) : NULL;
  if (loop != NULL && LOOP_DESCR_loophead(loop) == bb) {
    annot_remainder = ANNOT_Get(BB_annotations(bb), ANNOT_REMAINDERINFO);
  }
  if (h->innermost || h->irreducible || annot_remainder) {
    fprintf(file, "%sflags: [", indent);
    sep = "";
    if (h->innermost) {
      fprintf(file, "%s Inner", sep);
      sep = ",";
    } else if (h->irreducible) {
      fprintf(file, "%s Irreducible", sep);
      sep = ",";
    }
    if (annot_remainder != NULL) {
      fprintf(file, "%s Remainder", sep);
      sep = ",";
    }
    fprintf(file, " ]\n");
  }
  int pipelining = CG_LAO_pipelining;
  int renaming = CG_LAO_renaming;
  int boosting = CG_LAO_boosting;
  int preloading = CG_LAO_preloading;
  int l1missextra = CG_LAO_l1missextra;
  if (loop != NULL && annot_remainder == NULL) {
    // Collect information in loop #pragma
    int unroll_times = CG_LOOP_unroll_times_max;
    ANNOTATION *annot_pipeline = NULL;
    ANNOTATION *annot_unroll = NULL;
    ANNOTATION *annot_preload = NULL;
    // Try to access the #pragma pipeline or #pragma unroll arguments if any.
    ANNOTATION *annot_pragma = ANNOT_Get(BB_annotations(bb), ANNOT_PRAGMA);
    while (annot_pragma != NULL) {
      WN *wn = ANNOT_pragma(annot_pragma);
      if (WN_pragma(wn) == WN_PRAGMA_PIPELINE) {
        pipelining = WN_pragma_arg1(wn);
        renaming = WN_pragma_arg2(wn);
        annot_pipeline = annot_pragma;
      }
      if (WN_pragma(wn) == WN_PRAGMA_PRELOAD) {
        preloading = WN_pragma_arg1(wn);
        l1missextra = WN_pragma_arg2(wn);
        annot_preload = annot_pragma;
      }
      if (WN_pragma(wn) == WN_PRAGMA_UNROLL) {
        unroll_times = WN_pragma_arg1(wn);
        annot_unroll = annot_pragma;
      }
      annot_pragma = ANNOT_Get(ANNOT_next(annot_pragma), ANNOT_PRAGMA);
    }
    // If #pragma unroll disable unrolling 
    // and no #pragma pipeline, prevent kernel unrolling.
    if (   annot_unroll != NULL
        && unroll_times <= 1
        && annot_pipeline == NULL) {
      renaming = 1;
    }
  } else pipelining = renaming = 0;
  if (loopinfo != NULL) {
    // Emit the trip count if any.
#ifdef TARG_ST
    TN *trip_count_tn = LOOPINFO_primary_trip_count_tn(loopinfo);
#else 
    TN *trip_count_tn = LOOPINFO_trip_count_tn(loopinfo);
#endif
    if (trip_count_tn != NULL) {
      fprintf(file, "%stripcount: ", indent);
      tirex_emit_tn(trip_count_tn);
      fprintf(file, "\n");
    }
    // Emit the configure settings corrected by loopinfo.
    fprintf(file, "%sconfigure: {", indent);
    fprintf(file, " Pipelining: %d, Renaming: %d, Boosting: %d, PreLoading: %d, L1MissExtra: %d",
                  pipelining, renaming, boosting, preloading, l1missextra);
    if (0&&   trip_count_tn != NULL
        && TN_is_constant(trip_count_tn)
        && TN_value(trip_count_tn) < 64) {
      int tripmodulus = TN_value(trip_count_tn);
      fprintf(file, ", TripModulus: %d, TripResidue: %d", tripmodulus, 0);
    }
    fprintf(file, " }\n");
  }
}

void
tirex_emit_loopdep(BBSSTATE *h)
{ 
  OP_List op_list;
  for (BB_List::iterator bb_iter = (h->region).begin(); bb_iter != (h->region).end(); bb_iter++) {
    OP *op;
    FOR_ALL_BB_OPs(*bb_iter, op) {
      if (OP_node_id(op)) { op_list.push_back(op); }
    }
  }
  //
  // Emit the loop dependences, loop-carried if inner, else loop independent.
  if (op_list.size()) {
    sep = "";
    fprintf(file, "%snodes: [", indent);
    OP_List::iterator op_iter = op_list.begin();
    for (; op_iter != op_list.end(); op_iter++) {
      OP *op = *op_iter;
      uint32_t node_id = OP_node_id(op);
      fprintf(file, "%s N%u", sep, node_id);
      sep = ",";
    }
    fprintf(file, " ]\n");
    CG_DEP_Compute_Region_MEM_Arcs(h->region, h->isloopheader && h->innermost, false);
    bool no_arcs = true;
    op_iter = op_list.begin();
    for (; op_iter != op_list.end(); op_iter++) {
      OP *op1 = *op_iter;
      uint32_t op1_nid = OP_node_id(op1);
      if (_CG_DEP_op_info(op1)) {
        for (ARC_LIST *arcs = OP_succs(op1); arcs; arcs = ARC_LIST_rest(arcs)) {
          ARC *arc = ARC_LIST_first(arcs);
          CG_DEP_KIND kind = ARC_kind(arc);
          if (   ARC_is_mem(arc) && kind != CG_DEP_MEMVOL
              || kind == CG_DEP_MISC || kind == CG_DEP_PREFIN) {
            OP *op2 = ARC_succ(arc);
            int omega = ARC_omega(arc);
            int latency = ARC_latency(arc);
            CG_DEP_KIND kind = ARC_kind(arc);
            const char *type = "Other";
            if (kind == CG_DEP_MEMIN) type = "Flow";
            if (kind == CG_DEP_MEMANTI) type = "Anti";
            if (kind == CG_DEP_MEMREAD) type = "Input";
            if (kind == CG_DEP_MEMOUT) type = "Output";
            if (kind == CG_DEP_SPILLIN) type = "Spill";
            uint32_t op2_nid = OP_node_id(op2);
            if (no_arcs) fprintf(file, "%sarcs:\n", indent);
            fprintf(file, "%s- [ N%u, N%u, %s, %d, %d ]\n", indent, op1_nid, op2_nid, type, latency, omega);
            no_arcs = false;
          }
        }
      }
    }
    if (no_arcs) fprintf(file, "%sarcs: [ ]\n", indent);
    CG_DEP_Delete_Graph(&(h->region));
  }
}

// 
// TIREX for a BB.
void
tirex_emit_bb(BB *bb)
{
  fprintf(file, "%s- block: B%u\n", indent, BB_id(bb));
  indent_inc(2);
  RID *rid = BB_rid(bb);
  if (!region_seen[rid]) {
    region_seen[rid] = true;
  }
  if (BB_rid(bb)) {
    fprintf(file, "%sregion: R%u\n", indent, (unsigned)rid->id);
  }
  //fprintf(file, "%sloopdepth: %u\n", indent, (unsigned)loopforest_state[BB_id(bb)].loopdepth);
#if 0
  if (BB_loop_head_bb(bb)) {
    BB* head_bb = BB_loop_head_bb(bb);
    fprintf(file, "%sheader: B%u\n", indent, BB_id(head_bb));
  }
#endif
  // Emit the BB flags.
  sep = "";
  int flags = false;
  bool start = false;
  // Force the fully unrolled loop bodies to start a new scheduling region,
  // else the memory dependences will not be correct: bug pro-release-1-4-0-B/1.
  if (BB_unrolled_fully(bb)) {
    if (BB_loophead(bb)) start = true;
    else {
      // Fix bug pro-release-1-5-0-B/1
      ANNOTATION *annot = ANNOT_Get(BB_annotations(bb), ANNOT_LOOPINFO);
      if (annot) {
        LOOPINFO *info = ANNOT_loopinfo(annot);
        if (info) start = true;
      }
    }
  }
  if (start) {
    if (!flags++) fprintf(file, "%sflags: [", indent);
    fprintf(file, "%s Start", sep);
    sep = ",";
  }
  if (BB_entry(bb)) {
    if (!flags++) fprintf(file, "%sflags: [", indent);
    fprintf(file, "%s Entry", sep);
    sep = ",";
  }
  if (BB_exit(bb)) {
    if (!flags++) fprintf(file, "%sflags: [", indent);
    fprintf(file, "%s Exit", sep);
    sep = ",";
  }
  if (flags) fprintf(file, " ]\n");
  // Iteration.
  int instance = BB_unrollings(bb);
  if (instance > 0) {
    fprintf(file, "%sinstance: %d\n", indent, instance);
  }
  //
  // Emit the BB frequency.
  float frequency = BB_freq(bb);
  if (frequency > 0.0) {
    fprintf(file, "%sfrequency: %g\n", indent, frequency);
  }
  //
  // Emit the BB successors.
  sep = "";
  fprintf(file, "%ssuccessors: [", indent);
  BBLIST *bblist = NULL;
  FOR_ALL_BB_SUCCS(bb, bblist) {
    BB *succ_bb = BBLIST_item(bblist);
    float probability = BBLIST_prob(bblist);
    if (probability < 0.0) probability = 0.0;
    if (probability > 1.0) probability = 1.0;
    fprintf(file, "%s B%u: %g", sep, BB_id(succ_bb), probability);
    sep = ",";
  }
  fprintf(file, " ]\n");
  //
  // Emit the BB predecessors.
  sep = "";
  fprintf(file, "%spredecessors: [", indent);
  FOR_ALL_BB_PREDS(bb, bblist) {
    BB *pred_bb = BBLIST_item(bblist);
    fprintf(file, "%s B%u", sep, BB_id(pred_bb));
    sep = ",";
  }
  fprintf(file, " ]\n");
  //
  // Emit labels if any.
  if (BB_has_label(bb)) {
    fprintf(file, "%slabels: [", indent);
    sep = "";
    ANNOTATION *annot;
    for (annot = ANNOT_First(BB_annotations(bb), ANNOT_LABEL);
         annot != NULL; annot = ANNOT_Next(annot, ANNOT_LABEL)) {
      fprintf (file,"%s '%s'", sep, LABEL_name(ANNOT_label(annot)));
      sep = ",";
    }
    fprintf(file, " ]\n");
  }
  if (BB_length(bb)) {
    fprintf(file, "%soperations:\n", indent);
    OP *op = NULL;
    FOR_ALL_BB_OPs(bb, op) {
      tirex_emit_op(op);
    }
  }
  indent_dec(2);
}

// be/cg/cgemit.cxx:EMT_Visibility
static void
tirex_write_visibility ( ST* sym )
{
  ST_EXPORT eclass = ST_export(sym);
  const char *visibility =  NULL;
  switch (eclass)
    {
#ifdef AS_INTERNAL
    case EXPORT_INTERNAL:
      visibility = "internal";
      break;
#endif
#ifdef AS_HIDDEN
    case EXPORT_HIDDEN:
      visibility = "hidden";
      break;
#endif
#ifdef AS_PROTECTED
    case EXPORT_PROTECTED:
      visibity = "protected";
      break;
#endif
    }
  if (visibility)
    fprintf(file, "%svisibility: %s\n", indent, visibility);
}

static void
tirex_write_linkage ( ST* sym )
{
  if (ST_is_weak_symbol(sym)) {
    fprintf(file, "%slinkage: weak\n", indent);
  } 
  else if (!ST_is_export_local(sym)) {
    fprintf(file, "%slinkage: global\n", indent);
  }
}

// TIREX for the current PU.
void
tirex_emit_pu_code(ST *pu)
{
  OP_to_NID = OP_MAP32_Create();
  NID = 0;
  BB_to_LID = BB_MAP32_Create();
  LID = 0;
  OP_to_OID = OP_MAP32_Create();
  OID = 0;
  //
  MEM_POOL loop_pool;
  MEM_POOL_Initialize(&loop_pool, "TIREX loop descriptors", TRUE);
  MEM_POOL_Push(&loop_pool);
  LOOP_DESCR_Init_For_PU();
  Calculate_Dominators();
  LOOP_DESCR *loop = LOOP_DESCR_Detect_Loops(&loop_pool);
  while (loop != NULL) {
    BB *head_bb = LOOP_DESCR_loophead(loop);
    BB_MAP32_Set(BB_to_LID, head_bb, ++LID);
    loop = LOOP_DESCR_next(loop);
  }
  //
  // Emit the PU header
  const char *name = ST_name(pu);
  indent_dec(2);
  fprintf(file, "\n%s- function: '%s'\n", indent, name);
  indent_inc(2);
  fprintf(file, "%ssection: '%s'\n", indent, ST_name(text_base));
  tirex_write_linkage(pu);
  tirex_write_visibility(pu);
  BB_List entryBBs, exitBBs;
  for (BB *bb = REGION_First_BB; bb; bb = BB_next(bb)) {
    if (BB_entry(bb)) { entryBBs.push_back(bb); }
    if (BB_exit(bb)) { exitBBs.push_back(bb); }
  }
  fprintf(file, "%sentries: [", indent);
  sep = "";
  for (BB_List::iterator bb_iter = entryBBs.begin();
       bb_iter != entryBBs.end(); bb_iter++) {
    fprintf(file, "%s B%u", sep, BB_id(*bb_iter));
    sep = ",";
  }
  fprintf(file, " ]\n");
  sep = "";
  fprintf(file, "%sexits: [", indent);
  for (BB_List::iterator bb_iter = exitBBs.begin();
       bb_iter != exitBBs.end(); bb_iter++) {
    fprintf(file, "%s B%u", sep, BB_id(*bb_iter));
    sep = ",";
  }
  fprintf(file, " ]\n");
  //
  loopforest_state = tirex_build_loopforest();
  //
  // Emit the PU BBs.
  fprintf(file, "%sblocks:\n", indent);
  for (BB *bb = REGION_First_BB; bb; bb = BB_next(bb)) {
    tirex_emit_bb(bb);
  }
  //
  fprintf(file, "%sloops:\n", indent);
  // root body
  {
    BB_NUM hidx = 0;
    BBSSTATE *h = loopforest_state + hidx;
    fprintf(file, "%s- loop: ROOT\n", indent);
    indent_inc(2);
    fprintf(file, "%sbody: [ ", indent);
    tirex_dump_loopupperbody(loopforest_state, hidx);
    fprintf(file, " ]\n");
    tirex_loopupperbody(loopforest_state, &(h->region), hidx);
    tirex_emit_loopdep(h);
    indent_dec(2);
  }  
  // loops body
  for (BB *bb = REGION_First_BB; bb != NULL; bb = BB_next(bb)) {
    BB_NUM hidx = BB_id(bb);
    BBSSTATE *h = loopforest_state + hidx;
    if (h->isloopheader) {
      fprintf(file, "%s- loop: L%u\n", indent, h->loopidx);
      indent_inc(2);
      fprintf(file, "%sbody: [ ", indent);
      tirex_dump_loopupperbody(loopforest_state, hidx);
      fprintf(file, " ]\n");
      tirex_emit_loopdesc(bb);
      tirex_loopupperbody(loopforest_state, &(h->region), hidx);
      tirex_emit_loopdep(h);
      indent_dec(2);
    }
  }
  //
  OP_MAP_Delete(OP_to_OID);
  //
  BB_MAP_Delete(BB_to_LID);
  //
  Free_Dominators_Memory();
  MEM_POOL_Pop(&loop_pool);
  MEM_POOL_Delete(&loop_pool);
  //
  OP_MAP_Delete(OP_to_NID);
  //
  delete [] loopforest_state;
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Emit TIREX data
// simplified be/cg/cgemit.cxx: generate_elf_symbols == false, Assembly == true, Object_Code == false.

static unsigned last_inito_index = 1;
static unsigned pu_last_global_index = 1;
static unsigned bss_last_global_index = 1;
static std::map<ST *, int> symbol_seen;

// See be/cg/cgemit.cxx:Write_Label
static int64_t
tirex_write_label(LABEL_IDX lab, int section_idx, int64_t section_offset, int repeat)
{
  int address_size = Use_32_Bit_Pointers? 4: 8;
  const char *type = Use_32_Bit_Pointers? "word": "dword";
  ST *basesym = text_base;
  for (int i = 0; i < repeat; i++) {
    fprintf(file, "%s- %s: [ '%s' ]\n", indent, type, LABEL_name(lab));
    section_offset += address_size;
  }
  return section_offset;
}

// See be/cg/cgemit.cxx:Write_Symbol
static int64_t
tirex_write_symbol(ST *sym, int64_t sym_offset, int section_idx, int64_t section_offset, int repeat)
{
  int address_size = Use_32_Bit_Pointers? 4: 8;
  const char *type = Use_32_Bit_Pointers? "word": "dword";

  if (!Has_Base_Block(sym)) {
    Allocate_Object(sym);
  }

  if (ST_sclass(sym) == SCLASS_TEXT && !Has_Base_Block(sym)) {
    int32_t padding = repeat * address_size;
    if (padding > 0) {
      fprintf(file, "%s- space: %u\n", indent, padding);
    }
    return section_offset + padding;
  }

  ST *base_sym = sym;
  int64_t base_offset = 0;
  if (   Has_Base_Block(sym)
      && ST_is_export_local(sym)
      && Base_Offset_Is_Known(sym)
      && ST_class(sym) != CLASS_FUNC) {
    Base_Symbol_And_Offset(sym, &base_sym, &base_offset); 
  }
  base_offset += sym_offset;
  for (int i = 0; i < repeat; i++) {
    fprintf(file, "%s- %s: [ ", indent, type);
    if (ST_class(sym) == CLASS_CONST) {
      fprintf (file, "[");
      tirex_write_name(base_sym);
      if (base_offset) {
        fprintf (file, ", %+lld]", (long long)base_offset);
      } else {
        fprintf (file, "]");
      }
    } else
    if (ST_class(sym) == CLASS_FUNC) {
      fprintf (file, "[");
      tirex_write_name(sym);
      if (sym_offset) {
        fprintf (file, ", %+lld]", (long long)sym_offset);
      } else {
        fprintf (file, "]");
      }
    } else {
      fprintf (file, "[");
      tirex_write_name(sym);
      if (sym_offset) {
        fprintf (file, ", %+lld]", (long long)sym_offset);
      } else {
        fprintf (file, "]");
      }
    }
    fprintf (file, " ]\n");
    section_offset += address_size;
  }

  return section_offset;
}

// See be/cg/cgemit.cxx:Write_Symdiff
static int64_t
tirex_write_symdiff(LABEL_IDX lab1, ST_IDX sym2idx, int section_idx, int64_t section_offset, int repeat, int size)
{
  //TODO!
  assert(0);
  return section_offset;
}

// See be/cg/cgemit.cxx:Write_TCON
static int64_t
tirex_write_tcon(TCON *tcon, int section_idx, int64_t section_offset, int repeat)
{
  bool add_null = TCON_add_null(*tcon);
  int32_t offset32 = section_offset;
  // See emit/targ_em_const.cxx:Targ_Emit_Const( Asm_File, *tcon, add_null, repeat, section_offset );
  while (repeat) {
    char *p;
    int this_repeat, i;
    switch (TCON_ty(*tcon)) {
    case MTYPE_I1:
    case MTYPE_U1: {
        int64_t val = TCON_v0(*tcon) & 0xff;
        do {
          sep = "";
          this_repeat = MIN(repeat, 16);
          fprintf(file, "%s- byte: [", indent);
          for (i = 0; i < this_repeat; ++i) {
            fprintf(file, "%s %lld", sep, (long long)val);
            sep = ",";
          }
	  sep = "";
          fprintf(file, " ]\t# ");
          for (i = 0; i < this_repeat; ++i) {
            fprintf(file, "%s %1d", sep, TCON_v0(*tcon));
            sep = ",";
          }
	  fprintf(file, "\n");
	} while (repeat -= this_repeat);
      }
      repeat = 0;
      break;
    case MTYPE_I2:
    case MTYPE_U2: {
        int64_t val = TCON_v0(*tcon) & 0xffff;
        do {
          sep = "";
          this_repeat = MIN(repeat, 8);
          fprintf(file, "%s- hword: [", indent);
          for (i = 0; i < this_repeat; ++i) {
            fprintf(file, "%s %lld", sep, (long long)val);
            sep = ",";
          }
	  sep = "";
          fprintf(file, " ]\t# ");
          for (i = 0; i < this_repeat; ++i) {
            fprintf(file, "%s %1d", sep, TCON_v0(*tcon));
            sep = ",";
          }
	  fprintf(file, "\n");
        } while (repeat -= this_repeat);
      }
      repeat = 0;
      break;
    case MTYPE_I4:
    case MTYPE_U4: {
        int64_t val = TCON_v0(*tcon) & 0xffffffffllu;
        do {
          sep = "";
          this_repeat = MIN(repeat, 4);
          fprintf(file, "%s- word: [", indent);
          for (i = 0; i < this_repeat; ++i) {
            fprintf(file, "%s %ld", sep, (long)val);
            sep = ",";
          }
	  sep = "";
          fprintf(file, " ]\t# ");
          for (i = 0; i < this_repeat; ++i) {
            fprintf(file, "%s %1d", sep, TCON_v0(*tcon));
            sep = ",";
          }
	  fprintf(file, "\n");
        } while (repeat -= this_repeat);
      }
      repeat = 0;
      break;
    case MTYPE_I8:
    case MTYPE_U8: {
        TCON hi = Extract_LongLong_Hi(*tcon);
        TCON lo = Extract_LongLong_Lo(*tcon);
        int val1, val2;
        if (Target_Is_Little_Endian) {
          val1 = TCON_I4(lo);
          val2 = TCON_I4(hi);
        }
        else {
          val1 = TCON_I4(hi);
          val2 = TCON_I4(lo);
        }
        do {
          fprintf(file, "%s- word: [ 0x%x, 0x%x ]", indent, val1, val2);
	  fprintf(file, "\t# long long %lld\n", (long long)TCON_I8(*tcon));
        } while (repeat -= 1);
      }
      repeat = 0;
      break;
    case MTYPE_F4: {
        p = (char *) &TCON_R4(*tcon);
        fprintf(file, "%s- ascii: \"", indent);
        if (Same_Byte_Sex)
          for (i = 0; i < sizeof(TCON_R4(*tcon)); i++) fprintf (file, "\\x%02x", *(p+i));
        else
          for (i = sizeof(TCON_R4(*tcon)) -1 ; i >= 0; i--) fprintf (file, "\\x%02x", *(p+i));
        fprintf(file, "\"\t# float %#g\n", TCON_R4(*tcon));
      }
      --repeat;
      break;
    case MTYPE_C4: {
        p = (char *) &TCON_R4(*tcon);
        fprintf(file, "%s- ascii:\"", indent);
        for (i = 0; i < sizeof(TCON_R4(*tcon)); i++) fprintf (file, "\\x%02x", *(p+i));
        fprintf(file, "\"\t# complex float real part %#g\n", TCON_R4(*tcon));
        p = (char *) &TCON_IR4(*tcon);
        fprintf (file, "%s- ascii: \"", indent);
        for (i = 0; i < sizeof(TCON_IR4(*tcon)); i++) fprintf (file, "\\x%02x", *(p+i));
        fprintf(file, "\"\t# complex float imag part %#g\n", TCON_IR4(*tcon));
      }
      --repeat;
      break;
    case MTYPE_F8: {
        p = (char *) &TCON_R8(*tcon);
        fprintf (file, "%s- ascii: \"", indent);
        if (Same_Byte_Sex)
          for (i = 0; i < sizeof(TCON_R8(*tcon)); i++) fprintf (file, "\\x%02x", *(p+i));
        else 
          for (INT i = sizeof(TCON_R8(*tcon)) -1 ; i >= 0; i--) fprintf (file, "\\x%02x", *(p+i));
        fprintf(file, "\"\t# double %#g\n", TCON_R8(*tcon));
      }
      --repeat;
      break;
    case MTYPE_C8: {
        p = (char *) &TCON_R8(*tcon);
        fprintf (file, "%s- ascii: \"", indent);
        for (i = 0; i < sizeof(TCON_R8(*tcon)); i++) fprintf (file, "\\x%02x", *(p+i));
        fprintf(file, "\"\t# complex double real part %#g\n", TCON_R8(*tcon));
        p = (char *) & TCON_IR8(*tcon);
        fprintf (file, "%s- ascii: \"", indent);
        for (i = 0; i < sizeof(TCON_IR8(*tcon)); i++) fprintf(file, "\\x%02x", *(p+i));
        fprintf(file, "\"\t# complex double imag part %#g\n", TCON_IR8(*tcon));
      }
      --repeat;
      break;
    case MTYPE_STRING: {
        for (int count = 0; count < repeat; ++count) {
          // Targ_Emit_String(file, p, TCON_len(*tcon) + (add_null ? 1 : 0), 0 );
          p = Index_to_char_array(TCON_cp(*tcon));
          int len = TCON_len(*tcon) + add_null;
#define MAX_LEN 8
          bool has_control_char = false;
          for (i = 0; i < len - 1; ++i) {
            if (iscntrl(p[i]) || p[i] == '"' || p[i] == '\\') {
              has_control_char = true;
              break;
            }
          }
          if (len < 80 && p[len-1] == '\0' && !has_control_char) {
            fprintf(file, "%s- string: \"%s\"\n", indent, p);
          } else {
            int n_on_line = 0;
            char dbuf[(1+MAX_LEN)*4], *dptr = dbuf;
            for ( i=0; i<len; ++i ) {
              int ch = p[i];
              if (!n_on_line) {
                fprintf(file, "%s- byte: [", indent);
                sep = "";
              }
              fprintf(file, "%s 0x%x", sep, ch);
              sep = ",";
              dptr = Targ_Append_To_Dbuf(dptr, ch);
              ++n_on_line;
              if (n_on_line == MAX_LEN && i+1!=len) {
                *dptr = '\0';
                fprintf(file, " ]\t# %s\n", dbuf);
                dptr = dbuf;
                n_on_line = 0;
              }
            }
            *dptr = '\0';
            fprintf(file, " ]\t# %s\n", dbuf);
          }
#undef MAX_LEN
        }
      }
      repeat = 0;
      break;
    case MTYPE_FQ: {
        p = (char *) &TCON_R16(*tcon);
	fprintf (file, "%s- ascii: \"", indent);
	if (Same_Byte_Sex)
	  for (i = 0; i < sizeof(TCON_R8(*tcon)); i++) fprintf (file, "\\x%02x", *(p+i));
	else 
	  for (INT i = sizeof(TCON_R8(*tcon)) -1 ; i >= 0; i--) fprintf (file, "\\x%02x", *(p+i));
	fprintf(file, "\"\t# quad %#Lg\n", TCON_R16(*tcon));
      }
      --repeat;
      break;
    case MTYPE_V16I2: 
      fprintf(file, "%s- hword: %ld\n", indent, (long)(TCON_v0(*tcon) & 0xffff));
      fprintf(file, "%s- hword: %ld\n", indent, (long)((TCON_v0(*tcon)>>16) & 0xffff));
      fprintf(file, "%s- hword: %ld\n", indent, (long)(TCON_v1(*tcon) & 0xffff));
      fprintf(file, "%s- hword: %ld\n", indent, (long)((TCON_v1(*tcon)>>16) & 0xffff));
      fprintf(file, "%s- hword: %ld\n", indent, (long)(TCON_v2(*tcon) & 0xffff));
      fprintf(file, "%s- hword: %ld\n", indent, (long)((TCON_v2(*tcon)>>16) & 0xffff));
      fprintf(file, "%s- hword: %ld\n", indent, (long)(TCON_v3(*tcon) & 0xffff));
      fprintf(file, "%s- hword: %ld\n", indent, (long)((TCON_v3(*tcon)>>16) & 0xffff));
      --repeat;
      break;
    case MTYPE_V16I4: 
      fprintf(file, "%s- word: %ld\n", indent, (long)TCON_v0(*tcon));
      fprintf(file, "%s- word: %ld\n", indent, (long)TCON_v1(*tcon));
      fprintf(file, "%s- word: %ld\n", indent, (long)TCON_v2(*tcon));
      fprintf(file, "%s- word: %ld\n", indent, (long)TCON_v3(*tcon));
      --repeat;
      break;
    case MTYPE_V16I8: 
      fprintf(file, "%s- dword: %lld\n", indent, (long long)TCON_ll0(*tcon));
      fprintf(file, "%s- dword: %lld\n", indent, (long long)TCON_ll1(*tcon));
      --repeat;
      break;
    case MTYPE_V16F8: 
      // This looks like quite strange...
      fprintf(file, "%s- word: %ld\n", indent, (long)TCON_word0(Extract_Double_Lo(*tcon)));
      fprintf(file, "%s- word: %ld\n", indent, (long)TCON_word0(Extract_Double_Hi(*tcon))); 
      fprintf(file, "%s- word: %ld\n", indent, (long)TCON_word0(Extract_Double_Lo(*tcon)));
      fprintf(file, "%s- word: %ld\n", indent, (long)TCON_word0(Extract_Double_Hi(*tcon))); 
      --repeat;
      break;
    default:
      ErrMsg ( EC_Inv_Mtype, Mtype_Name(TCON_ty(*tcon)), "tirex_write_tcon" );
    }
  }
  if (TCON_ty(*tcon) == MTYPE_STRING) {
    section_offset += (Targ_String_Length (*tcon) + add_null) * repeat;
  } else {
    section_offset += TY_size(Be_Type_Tbl(TCON_ty(*tcon))) * repeat;
  }
  return section_offset;
}

// See common/com/em_elf.cxx:Em_Add_Zeros_To_Scn
static void
tirex_add_zeros(int section_idx, int64_t length, int64_t align)
{
#if 0
  pSCNINFO scninfo = em_scn[section_idx].scninfo;
  int64_t index = SCNINFO_offset(scninfo);
  /* roundup the size to the specified alignment */
  index = Roundup (index, align);
  if (SCNINFO_align(scninfo) < align) SCNINFO_align(scninfo) = align;
  int64_t newoffset = index + length;
  if (newoffset > SCNINFO_size(scninfo)) SCNINFO_size(scninfo) = newoffset;
  SCNINFO_offset(scninfo) = newoffset;
#endif
}

// See be/cg/cgemit.cxx:Write_INITV
static int64_t
tirex_write_initv(INITV_IDX invidx, int section_idx, int64_t section_offset)
{
  int i = 0;
  INITV_IDX ninv = 0;
  INITV inv = Initv_Table[invidx];

  TCON tcon;
  ST *st = NULL;
  LABEL_IDX lab = 0;
  switch (INITV_kind(inv)) {
  case INITVKIND_ZERO:
    tcon = Host_To_Targ (INITV_mtype(inv), 0);
    section_offset = tirex_write_tcon(&tcon, section_idx, section_offset, INITV_repeat2(inv));
    break;
  case INITVKIND_ONE:
    tcon = Host_To_Targ (INITV_mtype(inv), 1);
    section_offset = tirex_write_tcon(&tcon, section_idx, section_offset, INITV_repeat2(inv));
    break;
  case INITVKIND_VAL:
    section_offset = tirex_write_tcon(&INITV_tc_val(inv), section_idx, section_offset, INITV_repeat2(inv));
    break;
  case INITVKIND_SYMOFF:
    st = &St_Table[INITV_st(inv)];
    switch (ST_sclass(st)) {
      case SCLASS_AUTO:
        tcon = Host_To_Targ(MTYPE_I4, Offset_from_FP(st));
        section_offset = tirex_write_tcon (&tcon, section_idx, section_offset, INITV_repeat1(inv));
        break;
      case SCLASS_FORMAL:
      {
        ST *base = ST_base(st);
        int offset = Offset_from_FP(base) + ST_ofst(st);
        tcon = Host_To_Targ(MTYPE_I4, offset);
        section_offset = tirex_write_tcon(&tcon, section_idx, section_offset, INITV_repeat1(inv));
        break;
      }
      default:
        section_offset = tirex_write_symbol(st, INITV_ofst(inv), section_idx, section_offset, INITV_repeat1(inv));
        break;
    }
    break;
  case INITVKIND_LABEL:
    lab = INITV_lab(inv);
    section_offset = tirex_write_label(lab, section_idx, section_offset, INITV_repeat1(inv));
    break;
  case INITVKIND_SYMDIFF:
    section_offset = tirex_write_symdiff(INITV_lab1(inv), INITV_st2(inv),
                                         section_idx, section_offset, INITV_repeat1(inv), 4);
    break;
  case INITVKIND_SYMDIFF16:
    section_offset = tirex_write_symdiff(INITV_lab1(inv), INITV_st2(inv),
                                         section_idx, section_offset, INITV_repeat1(inv), 2);
    break;
  case INITVKIND_BLOCK:
    for (i = 0; i < INITV_repeat1(inv); i++) {
      for (ninv = INITV_blk(inv); ninv; ninv = INITV_next(ninv)) {
        section_offset = tirex_write_initv(ninv, section_idx, section_offset);
      }
    }
    break;
  case INITVKIND_PAD:
    if ((INITV_pad(inv)*INITV_repeat1(inv) > 0)) {
      fprintf(file, "%s- space: %u\n", indent, INITV_pad(inv) * INITV_repeat1(inv));
    }
    //Em_Add_Zeros_To_Scn (scn, INITV_pad(inv) * INITV_repeat1(inv), 1);
    tirex_add_zeros(section_idx, INITV_pad(inv) * INITV_repeat1(inv), 1);
    section_offset += INITV_pad(inv) * INITV_repeat1(inv);
  default:
    break;
  }

  return section_offset;
}

// See be/cg/cgemit.cxx:Print_Label
static void
tirex_print_object(ST *sym)
{
  ST *base_sym = sym;
  int64_t base_offset = 0;
  //
  Base_Symbol_And_Offset (sym, &base_sym, &base_offset);
  indent_dec(2);
  fprintf(file, "\n%s- object: ", indent);
  tirex_write_name(sym);
  fprintf(file, "\n");
  indent_inc(2);
  fprintf(file, "%ssize: %lld\n", indent, (long long)TY_size(ST_type(sym)));
  fprintf(file, "%salign: %d\n", indent, TY_align(ST_type(sym)));
  //
  fprintf(file, "%ssection: '%s'\n", indent, ST_name(current_section));
  //
  tirex_write_linkage( sym );
  tirex_write_visibility( sym );
  //
}

// See be/cg/cgemit.cxx:Write_INITO
static void
tirex_write_inito(INITO* inop, int section_idx, int64_t section_offset)
{
  ST *base = NULL;
  int64_t offset = 0;
  INITO ino = *inop;

  Base_Symbol_And_Offset(INITO_st(ino), &base, &offset);
  if (offset > section_offset) {
    //fprintf(file, "%s- space: %u\n", indent, (unsigned)(offset - section_offset));
    //Em_Add_Zeros_To_Scn ( scn, inito_ofst - scn_ofst, 1 );
    tirex_add_zeros(section_idx, offset - section_offset, 1);
    section_offset = offset;
  } else assert(offset >= section_offset);

  ST *sym = INITO_st(ino);
  char *name = ST_name(sym);
  if (name != NULL && *name != 0) {
    tirex_print_object(sym);
  } else {
    fprintf(file, "%s# ERROR: null symbol name in tirex_write_inito\n", indent);
  }

  fprintf(file, "%sinit:\n", indent);
  int64_t initial_offset = section_offset;
  if (INITO_val(ino) == (INITO_IDX)NULL) {
    if (ST_class(sym) == CLASS_CONST) {
      section_offset = tirex_write_tcon(&ST_tcon_val(sym), section_idx, section_offset, 1);
    }
  } else {
    INITV_IDX inv;
    FOREACH_INITV (INITO_val(ino), inv) {
      section_offset = tirex_write_initv(inv, section_idx, section_offset);
    }
  }
  if (section_offset - initial_offset > 50) 
    fprintf(file, "%s# end of initialization for '%s'\n", indent, name);
}

// See be/cg/cgemit.cxx:Print_Common
static void
tirex_emit_common(ST *sym)
{
  ST *base = NULL;
  int64_t offset = 0;
  Base_Symbol_And_Offset(sym, &base, &offset);
  if (sym != base && ST_sclass(base) == SCLASS_COMMON) {
    if (!symbol_seen[base]) {
      tirex_emit_common(base);
    }
    return;
  }
  if (TY_size(ST_type(sym)) > 0) {
    if (ST_is_weak_symbol(sym)) {
      fprintf(file, "%sweak: ", indent);
      tirex_write_name(sym);
      fprintf(file, "\n");
    }
    indent_dec(2);
    fprintf(file, "\n%s- common: ", indent);
    tirex_write_name(sym);
    indent_inc(2);
    fprintf(file, "\n");
    fprintf(file, "%ssize: %lld\n", indent, (long long)TY_size(ST_type(sym)));
    fprintf(file, "%salign: %d\n", indent, TY_align(ST_type(sym)));
    symbol_seen[sym] = true;
  }
}

// See be/cg/cgemit.cxx:EMT_Put_Elf_Symbol
static void
tirex_emit_symbol(ST *sym)
{
  if (symbol_seen[sym]) return;
  if (0&& ST_class(sym) == CLASS_FUNC) {
    fprintf(file, "%stype: { ", indent);
    tirex_write_name(sym);
    fprintf(file, ": function }\n");
  } else
  if (ST_class(sym) == CLASS_VAR && ST_sclass(sym) == SCLASS_COMMON) {
    tirex_emit_common(sym);
  }
  symbol_seen[sym] = true;
}

// See be/cg/cgemit.cxx:Init_Section
static void
tirex_init_section(ST *section)
{
  if (symbol_seen[section]) return;
  symbol_seen[section] = true;
  indent_dec(2);
  fprintf(file, "\n%s- section: '%s'\n", indent, ST_name(section));
  indent_inc(2);
  // CGEMIT_Prn_Scn_In_Asm(st, scn_type, scn_flags, scn_entsize, section);
  int64_t section_type = Get_Section_Elf_Type(STB_section_idx(section));
  int64_t section_flags = Get_Section_Elf_Flags(STB_section_idx(section));
  int64_t align = STB_align(section);
  sep = "";
  fprintf(file, "%sflags: [", indent);
  if (section_flags & SHF_WRITE) {
    fprintf(file, "%s Write", sep);
    sep = ",";
  }
  if (section_flags & SHF_ALLOC) {
    fprintf(file, "%s Alloc", sep);
    sep = ",";
  }
  if (section_flags & SHF_EXECINSTR) {
    fprintf(file, "%s Exec", sep);
    sep = ",";
  }
  if (section_flags & SHF_TLS) {
    fprintf(file, "%s TLS", sep);
    sep = ",";
  }
  fprintf(file, " ]\n");
  fprintf(file, "%salign: %d\n", indent, (int)align);
}

// See be/cg/cgemit.cxx:Change_Section_Origin
static void
tirex_change_section(ST *section, int64_t offset)
{
  //if (section != current_section) {
    //indent_dec(2);
    //fprintf(file, "%s- object:\t# change_section %s\n", indent, ST_name(section));
    //fprintf(file, "\n%s- object:\n", indent);
    //indent_inc(2);
    //fprintf(file, "%ssection: '%s'\n", indent, ST_name(section));
  //}
  //fprintf(file, "%sorigin: 0x%llx\n", indent, (long long)offset);
  //fprintf(file, "%salign: 0\n", indent);
  current_section = section;
}

// Copied from be/cg/cgemit.cxx
inline bool section_lt (ST *s1, ST* s2)
{
  return Base_Symbol(s1) < Base_Symbol(s2);
}
inline bool offset_lt (ST *s1, ST* s2)
{
  ST *base1 = NULL, *base2 = NULL;
  int64_t offset1 = 0, offset2 = 0;
  Base_Symbol_And_Offset(s1, &base1, &offset1);
  Base_Symbol_And_Offset(s2, &base2, &offset2);
  return offset1 < offset2;
}
inline bool size_lt (ST *s1, ST* s2)
{
  return TY_size(ST_type(s1)) < TY_size(ST_type(s2));
}

// See be/cg/cgemit.cxx:Process_Initos_And_Literals
static void
process_inittos_and_literals(SYMTAB_IDX stab)
{
  static vector<bool> st_processed;
  if (st_processed.size() != ST_Table_Size(GLOBAL_SYMTAB)) {
    st_processed.resize(ST_Table_Size(GLOBAL_SYMTAB), false);
  }

  typedef std::map <ST_IDX,INITO*> ST_INITO_MAP;
  ST_INITO_MAP st_inito_map;
  vector<ST*> st_list;
  unsigned index;

  // First walk the INITOs from the global table
  for (index = last_inito_index; index < INITO_Table_Size(GLOBAL_SYMTAB); ++index) {
    INITO* ino = &Inito_Table(GLOBAL_SYMTAB, index);
    ST* st = INITO_st(ino);
    if (ST_is_not_used(st) ||
        ST_sclass(st) == SCLASS_EXTERN ||
        ST_sclass(st) == SCLASS_DISTR_ARRAY) {
      continue;
    }
    st_list.push_back(st);
    st_inito_map[ST_st_idx(st)] = ino;
  }
  last_inito_index = INITO_Table_Size(GLOBAL_SYMTAB);
  
  // Then walk the INITOs from the local table
  if (stab != GLOBAL_SYMTAB) {
    for (index = 1; index < INITO_Table_Size(stab); ++index) {
      INITO* ino = &Inito_Table(stab, index);
      ST* st = INITO_st(ino);
      if (ST_is_not_used(st) ||
          ST_sclass(st) == SCLASS_EXTERN) {
        continue;
      }
      st_list.push_back(st);
      st_inito_map[ST_st_idx(st)] = ino;
    }
  }

  // Then walk the CONSTANTs from the global table
  for (index = 1; index < ST_Table_Size(GLOBAL_SYMTAB); ++index) {
    ST* st = &St_Table(GLOBAL_SYMTAB,index);
    if (ST_class(st) == CLASS_CONST && !st_processed[ST_index(st)]) {
      ST *base = NULL;
      int64_t offset = 0;
      Base_Symbol_And_Offset(st, &base, &offset);
      if (ST_class(base) != CLASS_BLOCK || !STB_section(base)) continue;
      if (Emit_Global_Data && SEC_is_merge(STB_section_idx(base))) continue;
      st_list.push_back(st);
    }
  }

  // Sort the st_list
  stable_sort (st_list.begin(), st_list.end(), size_lt);
  stable_sort (st_list.begin(), st_list.end(), offset_lt);
  stable_sort (st_list.begin(), st_list.end(), section_lt);

  // Emit the st_list
  vector<ST*>::iterator st_iter;
  for (st_iter = st_list.begin(); st_iter != st_list.end(); ++st_iter) {
    ST *st = *st_iter;
    ST *base = NULL;
    int64_t offset = 0;
    ST_INITO_MAP::iterator st_inito_entry = st_inito_map.find(ST_st_idx(st));
    if (st_inito_entry != st_inito_map.end()) {
      INITO* ino = (*st_inito_entry).second;
      Base_Symbol_And_Offset(st, &base, &offset);
      if (ST_sclass(base) == SCLASS_EXTERN) continue;
      if (ST_class(base) != CLASS_BLOCK) continue; // not allocated CLASS_VAR
      tirex_init_section(base);
      tirex_change_section(base, offset);
      tirex_write_inito(ino, STB_scninfo_idx(base), offset);
    } else {
      st_processed[ST_index(st)] = TRUE;
      Base_Symbol_And_Offset(st, &base, &offset);
      if (ST_class(base) != CLASS_BLOCK) continue; // not allocated CLASS_VAR
      tirex_init_section(base);
      tirex_change_section(base, offset);
      fprintf(file, "\n- object: '.LC%u'\n", (unsigned)ST_IDX_index(ST_st_idx(st)));
      fprintf(file, "%ssize: %lld\n", indent, (long long)TY_size(ST_type(st)));
      fprintf(file, "%salign: %u\n", indent, (unsigned)TY_align (ST_type (st)));
      fprintf(file, "%ssection: %s\n", indent, ST_name(base));
      fprintf(file, "%sinit:\n", indent);
      tirex_write_tcon(&ST_tcon_val(st), STB_scninfo_idx(base), offset, 1);
    }
  }
}

// See be/cg/cgemit.cxx:Process_Bss_Data
static void
process_bss_data(SYMTAB_IDX stab)
{
  vector<ST*> bss_list;
  unsigned index = stab == GLOBAL_SYMTAB? bss_last_global_index: 1;
  for (; index < ST_Table_Size(stab); ++index) {
    ST* sym = &St_Table(stab, index);
    if (ST_class(sym) == CLASS_BLOCK) continue;
    if (!Has_Base_Block(sym)) continue;
    if (ST_sclass(sym) == SCLASS_UGLOBAL ||
        ST_sclass(sym) == SCLASS_FSTATIC ||
        ST_sclass(sym) == SCLASS_PSTATIC) {
      bss_list.push_back (sym);
    }
  }
  if (stab == GLOBAL_SYMTAB) {
    bss_last_global_index = ST_Table_Size(GLOBAL_SYMTAB);
  }

  // Sort the bss_list
  stable_sort (bss_list.begin(), bss_list.end(), size_lt);
  stable_sort (bss_list.begin(), bss_list.end(), offset_lt);
  stable_sort (bss_list.begin(), bss_list.end(), section_lt);

  // Emit the bss_list
  vector<ST*>::iterator bssp;
  int64_t pad = 0;
  for (bssp = bss_list.begin(); bssp != bss_list.end(); ++bssp) {
    ST* sym = *bssp;
    ST *base = NULL;
    int64_t offset = 0;
    Base_Symbol_And_Offset(sym, &base, &offset);
    if (ST_class(base) != CLASS_BLOCK || !STB_section(base)) continue;
    if (!STB_nobits(base)) continue;
    tirex_change_section(base, offset);
    tirex_print_object(sym);
    if (pad > 0)  {
      //fprintf(file, "%s- space: %u\n", indent, (unsigned) pad);
    }
    if (bssp+1 != bss_list.end()) {
      ST* next_sym = *(bssp+1);
      ST* next_base = NULL;
      int64_t next_offset = 0;
      Base_Symbol_And_Offset(next_sym, &next_base, &next_offset);
      if (next_base == base && next_offset == offset) continue;
      if (next_base == base && next_offset < (offset+TY_size(ST_type(sym)))) 
	pad = next_offset - offset;
    }
  }
}
// See be/cg/cgemit.cxx:EMT_Begin_File
void
tirex_emit_first(void)
{
  unsigned CG_LAO_convention = Target_ABI;
  fprintf(file, "%sprogram: # compiling %s for %s\n", indent, Src_File_Name, Isa_Name(Target_ISA));
  fprintf(file, "\n%s- optimize:\n", indent);
  indent_inc(2);
  fprintf(file, "%sprocessor: %s\n", indent, Targ_Name(Target));
  fprintf(file, "%sconvention: %u\n", indent, Target_ABI);
  if (CG_LAO_activation) {
    fprintf(file, "%sactivation: [", indent); sep = "";
    if (CG_LAO_activation & 0x1) { fprintf(file, "%sEncode", sep); sep = ","; }
    if (CG_LAO_activation & 0x2) { fprintf(file, "%sPostPass", sep); sep = ","; }
    if (CG_LAO_activation & 0x4) { fprintf(file, "%sRegAlloc", sep); sep = ","; }
    if (CG_LAO_activation & 0x8) { fprintf(file, "%sPrePass", sep); sep = ","; }
    if (CG_LAO_activation & 0x10) { fprintf(file, "%sSSAForm", sep); sep = ","; }
    fprintf(file, "]\n");
  }
  if (CG_LAO_conversion) {
    fprintf(file, "%sconversion: [", indent); sep = "";
    if (CG_LAO_conversion & 0x1) { fprintf(file, "%sFolding", sep); sep = ","; }
    if (CG_LAO_conversion & 0x2) { fprintf(file, "%sCleaning", sep); sep = ","; }
    if (CG_LAO_conversion & 0x4) { fprintf(file, "%sSemiPruned", sep); sep = ","; }
    if (CG_LAO_conversion & 0x8) { fprintf(file, "%sSigmaGoTo", sep); sep = ","; }
    if (CG_LAO_conversion & 0x10) { fprintf(file, "%sDedicated", sep); sep = ","; }
    fprintf(file, "]\n");
  }
  if (CG_LAO_coalescing) {
    fprintf(file, "%scoalescing: [", indent); sep = "";
    if (CG_LAO_coalescing & 0x1) { fprintf(file, "%sSreedhar", sep); sep = ","; }
    if (CG_LAO_coalescing & 0x2) { fprintf(file, "%sBoissinot", sep); sep = ","; }
    if (CG_LAO_coalescing & 0x4) { fprintf(file, "%sDecoalesce", sep); sep = ","; }
    if (CG_LAO_coalescing & 0x8) { fprintf(file, "%sVirtualize", sep); sep = ","; }
    if (CG_LAO_coalescing & 0x10) { fprintf(file, "%sCongruence", sep); sep = ","; }
    if (CG_LAO_coalescing & 0x20) { fprintf(file, "%sSeqCopies", sep); sep = ","; }
    if (CG_LAO_coalescing & 0x40) { fprintf(file, "%sIterated", sep); sep = ","; }
    if (CG_LAO_coalescing & 0x80) { fprintf(file, "%sFlorent", sep); sep = ","; }
    fprintf(file, "]\n");
  }
  if (CG_LAO_rewriting) {
    fprintf(file, "%srewriting: [", indent); sep = "";
    if (CG_LAO_rewriting & 0x1) { fprintf(file, "%sRange", sep); sep = ","; }
    if (CG_LAO_rewriting & 0x2) { fprintf(file, "%sBWLU", sep); sep = ","; }
    fprintf(file, "]\n");
  }
  if (CG_LAO_scheduling) {
    fprintf(file, "%sscheduling: [", indent); sep = "";
    if (CG_LAO_scheduling & 0x1) { fprintf(file, "%sUnwinding", sep); sep = ","; }
    if (CG_LAO_scheduling & 0x2) { fprintf(file, "%sInsertion", sep); sep = ","; }
    if (CG_LAO_scheduling & 0x4) { fprintf(file, "%sIterative", sep); sep = ","; }
    fprintf(file, "]\n");
  }
#if 0
  if (CG_LAO_allocation) {
    fprintf(file, "%sallocation: [", indent); sep = "";
    fprintf(file, "]\n");
  }
  if (CG_LAO_rcmssolving) {
    fprintf(file, "%srcmsSolving: [", indent); sep = "";
    fprintf(file, "]\n");
  }
  if (CG_LAO_logtimeout) {
    fprintf(file, "%slogTimeOut: [", indent); sep = "";
    fprintf(file, "]\n");
  }
#endif
}

// See be/cg/cgemit.cxx:EMT_Emit_PU
void
tirex_emit_pu(ST *pu)
{
  ST *sym;
  unsigned index;

  // Initialize any new global sections.
  for (index = pu_last_global_index; index < ST_Table_Size(GLOBAL_SYMTAB); ++index) {
    ST* sym = &St_Table(GLOBAL_SYMTAB, index);
    if (ST_class(sym) == CLASS_BLOCK && STB_section(sym)) {
      tirex_init_section(sym);
    }
    if (ST_sclass(sym) == SCLASS_COMMON) {
      if (ST_is_not_used (sym)) continue;
      tirex_emit_symbol(sym);
    }
  }
  pu_last_global_index = ST_Table_Size(GLOBAL_SYMTAB);

  // Emit global bss first so .org is correct.
  process_bss_data(GLOBAL_SYMTAB);

  // Initialize any sections that might have been created by the backend.
  FOREACH_SYMBOL (CURRENT_SYMTAB, sym, index) {
    ST *base = Base_Symbol(sym);
    if (ST_class(base) == CLASS_BLOCK && STB_section(base)) {
      tirex_init_section(base);
    }
  }

  // See be/cg/cgemit.cxx:Setup_Text_Section_For_PU
  static ST *orig_text_base;
  if (text_base == NULL) {
    text_base = SEC_block(_SEC_TEXT);
  }
  orig_text_base = text_base;
  if (Section_For_Each_Function) {
    /* create new text section */
    text_base = Copy_ST(orig_text_base);
    Set_ST_blk(text_base, Copy_BLK(ST_blk(orig_text_base)));
    Set_STB_size (text_base, 0);
    Set_STB_scninfo_idx(text_base, 0);
    Set_STB_section_idx(text_base, STB_section_idx(orig_text_base));
    tirex_init_section(text_base);
  } else if (ST_base(pu) != text_base) {
    text_base = ST_base(pu);
  }
  current_section = text_base;

  FOREACH_SYMBOL (CURRENT_SYMTAB, sym, index) {
    if (ST_is_not_used(sym)) continue;
    if (ST_sclass(sym) == SCLASS_COMMON) {
      tirex_emit_symbol(sym);
    }
  }

  tirex_emit_pu_code(pu);

  // Emit the initialized data associated with this PU.
  process_inittos_and_literals(CURRENT_SYMTAB);
  process_bss_data(CURRENT_SYMTAB);

}

// See be/cg/cgemit.cxx:EMT_End_File
void
tirex_emit_last(void)
{
  ST *sym; int i;
  FOREACH_SYMBOL (GLOBAL_SYMTAB, sym, i) {
    if (ST_class(sym) == CLASS_BLOCK && STB_section(sym)) {
      if (SEC_is_merge(STB_section_idx(sym))) continue;
      tirex_init_section(sym);
    }
    if (ST_sclass(sym) == SCLASS_COMMON) {
      if (ST_is_not_used (sym)) continue;
      tirex_emit_symbol(sym);
    }
  }
  if (Emit_Global_Data) {
    // create dummy symbol to represent the section
    FOREACH_SYMBOL (GLOBAL_SYMTAB, sym, i) {
      if (ST_class(sym) != CLASS_BLOCK) continue;
      if (!STB_section(sym)) continue;
      if (SEC_is_merge(STB_section_idx(sym))) continue;
      char *newname = Index_To_Str(Save_Str2(ST_name(sym), ".symbol"));
      tirex_change_section(sym, 0);
      indent_dec(2);
      fprintf(file, "\n%s- object: '%s'\n", indent, newname);
      indent_inc(2);
      fprintf(file, "%sglobal: '%s'\n", indent, newname);
    }
  }
  process_bss_data(GLOBAL_SYMTAB);
  process_inittos_and_literals(GLOBAL_SYMTAB);
  process_inittos_and_literals(GLOBAL_SYMTAB);
  FOREACH_SYMBOL (GLOBAL_SYMTAB, sym, i) {
    if (ST_class(sym) == CLASS_NAME) {
      if (ST_emit_symbol(sym)) {
        tirex_emit_symbol(sym);
      }
    }
  }
  indent_dec(2);
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Emit TIREX code.

// Begin processing module (compilation unit)
void
tirex_init(FILE *emit_file)
{
  indent_depth = 0;
  indent[indent_depth] = '\0';
  stage = CG_TIREX_stage;
  if (emit_file == NULL) stage = 0;
  else file = emit_file;
  text_base = NULL;
  current_section = NULL;
  last_inito_index = 1;
  pu_last_global_index = 1;
  bss_last_global_index = 1;
  symbol_seen.clear();
  //
  if (stage > 0) {
    tirex_emit_first();
  }
}

void
tirex_emit_pu(int emit_stage)
{
  if (emit_stage <= 0 || emit_stage != stage) return;
  //
  region_seen.clear();
  tirex_emit_pu(Get_Current_PU_ST());
}

// End processing module.
// We emit remaining static data.
void
tirex_fini(void)
{
  if (stage > 0) {
    tirex_emit_last();
  }
  indent_depth = 0;
  indent[indent_depth] = '\0';
}

