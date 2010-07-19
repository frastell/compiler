//-*-c++-*-

/*
 * Copyright 2008 PathScale, LLC.  All Rights Reserved.
 */

/*
 *  Copyright (C) 2006. QLogic Corporation. All Rights Reserved.
 */

/*
 * Copyright 2002, 2003, 2004, 2005, 2006 PathScale, Inc.  All Rights Reserved.
 */

// ====================================================================
// ====================================================================
//
// Module: opt_bdce.cxx
// $Revision: 1.40 $
// $Date: 05/10/27 14:00:53-07:00 $
// $Author: fchow@fluorspar.internal.keyresearch.com $
// $Source: be/opt/SCCS/s.opt_bdce.cxx $
//
// ====================================================================
//
// Copyright (C) 2000, 2001 Silicon Graphics, Inc.  All Rights Reserved.
//
/*
   Path64 is free software; you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   Path64 is distributed in the hope that it will be useful, but WITHOUT
   ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
   or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
   License for more details.

   You should have received a copy of the GNU General Public License
   along with Path64; see the file COPYING.  If not, write to the Free
   Software Foundation, 51 Franklin Street, Fifth Floor, Boston, MA
   02110-1301, USA.

   Special thanks goes to SGI for their continued support to open source

*/
//
// ====================================================================
//
// Description:
//
// Bitwise Dead Code Elimination - For now, this is only used to
// identify useless CVTLs.  It is intended that this will be extended
// to replace the regular DCE phase in future.
//
// The algorithm works like this. All variable nodes carry a bit mask
// that tells if each bit is live.  Each operator in an expression tree
// carries the same bit mask.  (In effect, all coderep nodes carry this
// bit mask.) We initialize all the bits to dead (0).  We propagate
// live bits starting at the return statements.  The paths of
// propagation are: use-def edges of variables, expression tree edges,
// control dependences.  In addition, in regions of the CFG where it
// never leads to an exit (i.e. infinite loops), all statements are
// regarded as live.
//
// If the root of an expression tree has live bits, we propagate the
// liveness top-down in the expression tree.  If the use of a variable
// has live bits, we propagate the liveness to the def statement of the
// variable.  
//
// After the liveness propagation is done, we conduct a pass over the
// program.  If a CVTL only affects bits that are dead, we delete the
// CVTL (dead CVTLs).  If a CVTL is not dead, we analyze the value of
// its operand.  This analysis can be global scope using SSA's use-defs
// and phis.  If we determine that the  CVTL is redundant, we also
// delete it.
//
// In addition, during the analysis phase, a Usecnt value is determined
// for each expression node, indicating whether the node is used 0, 1,
// or more than 1 times.  In order to prevent node uses from being
// counted more than once, a node are only counted when the statement
// it appears in is declared live.  (A few STID statements are not ever
// declared live during the analysis phase.  These are handled
// afterwards.)  Uses in phi nodes are handled the first time the phi
// LHS variable is assigned live bits.
//
// During the deletion of dead statements and CVTL, some definitions of
// variables (those that has a unique use closely following their
// definitions) are copy propagated, in order to clean up the output
// of the EPRE phase.
//
// ====================================================================
// ====================================================================


#ifdef USE_PCH
#include "opt_pch.h"
#endif // USE_PCH
#pragma hdrstop


#define __STDC_LIMIT_MACROS
#include <stdint.h>
#include "defs.h"
#include "errors.h"
#include "erglob.h"
#include "glob.h"	// for Cur_PU_Name
#include "mempool.h"
#include "tracing.h"	/* for TFile */
#include "cxx_memory.h"
#include "config_targ.h" // needed for Pointer_type

#include "opt_defs.h"
#include "opt_cfg.h"
#include "opt_ssa.h"
#include "opt_main.h"
#include "opt_mu_chi.h"
#include "opt_sym.h"
#include "opt_htable.h"
#include "bb_node_set.h"
#include "opt_bdce.h"

#if HAVE_ALLOCA_H
#include <alloca.h>
#endif

/* CVTL-RELATED start (performance) */

// ====================================================================
//  Initialize_stmts_dead - initialize the SRF_LIVE_STMT bit of all statements
// ====================================================================
void
BITWISE_DCE::Initialize_stmts_dead(void)
{
  CFG_ITER cfg_iter(Cfg());
  BB_NODE *bb;
  // visit all blocks
  FOR_ALL_NODE( bb, cfg_iter, Init() ) {
    // visit all statements
    STMTREP_ITER stmt_iter(bb->Stmtlist());
    STMTREP *stmt;
    FOR_ALL_NODE(stmt, stmt_iter, Init()) {
      switch (stmt->Opr()) {
      case OPR_LABEL:
      case OPR_PRAGMA:
      case OPR_ALTENTRY:
      case OPR_GOTO:
        continue;	// these statements are live no matter what
      default:
	stmt->Reset_live_stmt();
      }
    }
  }
}

// ====================================================================
// Operators_without_dependency - these statement operators cannot be
// deleted even if there is no dependency on it.
// ====================================================================
BOOL
BITWISE_DCE::Operators_without_dependency(OPERATOR opr)
{
  if (OPERATOR_is_call(opr))
    return TRUE;
  switch (opr) {
  case OPR_ASM_STMT:
  case OPR_ASSERT:
  case OPR_PREFETCH:
  case OPR_XPRAGMA:
  case OPR_REGION:
  case OPR_FORWARD_BARRIER:
  case OPR_BACKWARD_BARRIER:
  case OPR_DEALLOCA:
  case OPR_EVAL:	// for EVAL, can alternatively use strategy in DCE
#ifdef TARG_ST
  case OPR_AFFIRM:
#endif
    return TRUE;
  default:
    return FALSE;
  }
}

// ====================================================================
// Bitmask_of_size - forms a bit mask of 1's for the number of bits
// ====================================================================
UINT64
BITWISE_DCE::Bitmask_of_size(INT32 vsize)
{
  Is_True(vsize != 0, ("BITWISE_DCE::Bitmask_of_size: size cannot be 0"));
  if (vsize >= 64)
    return UINT64_MAX;
  return ((UINT64) 1 << vsize) - 1;
}

// ====================================================================
// Fill_lower_bits - return the same bit mask with all 0 bits to the left
// of the most significant bit set to 1
// ====================================================================
UINT64
BITWISE_DCE::Fill_lower_bits(UINT64 bitmask)
{
  bitmask |= bitmask >> 32;
  bitmask |= bitmask >> 16;
  bitmask |= bitmask >>  8;
  bitmask |= bitmask >>  4;
  bitmask |= bitmask >>  2;
  bitmask |= bitmask >>  1;
  return bitmask;
}

// ====================================================================
// Bits_in_type - return a bit mask representing all the bits in the given
// mtype; if type size is larger than 64 bits, must be a floating point
// type, and will return UINT64_MAX.
// ====================================================================
inline UINT64
BITWISE_DCE::Bits_in_type(MTYPE dt)
{
#if !defined( KEY)  || defined(TARG_ST)
  Is_True(dt != MTYPE_UNKNOWN, ("BITWISE_DCE::Bits_in_type: type is unknown"));
#endif
#ifdef TARG_ST
  //[TB] For multiple result mtype treat as VOID
  if (dt == MTYPE_V || dt == MTYPE_M ||
      MTYPE_is_composed(dt))
    return UINT64_MAX;
#else
  if (dt == MTYPE_V || dt == MTYPE_M || dt == MTYPE_UNKNOWN)
    return UINT64_MAX;
#endif
  UINT64 vsize = MTYPE_size_min(dt);
  return Bitmask_of_size(vsize);
}

// ====================================================================
// Bits_in_coderep_result - return the bit mask representing all the bits
// in the result of the coderep node; the purpose is to take care of the 
// pecularity of OPR_CVT when its result type is smaller than its desc type.
// ====================================================================
inline UINT64
BITWISE_DCE::Bits_in_coderep_result(CODEREP *cr)
{
  if (cr->Kind() == CK_OP && cr->Opr() == OPR_CVT) {
    MTYPE dsctyp = cr->Dsctyp();
    MTYPE dtyp = cr->Dtyp();
    if (MTYPE_is_integral(dtyp) && MTYPE_is_integral(dsctyp))
      return Bitmask_of_size(MAX(MTYPE_size_min(dtyp), MTYPE_size_min(dsctyp)));
    return Bitmask_of_size(MTYPE_size_min(dtyp));
  }
  return Bits_in_type(cr->Dtyp());
}

// ====================================================================
// Bits_in_var - return a bit mask representing all the bits in the variable
// if variable size is larger than 64 bits, must be a floating point
// type, and will return UINT64_MAX.
// ====================================================================
UINT64
BITWISE_DCE::Bits_in_var(CODEREP *v)
{
  AUX_STAB_ENTRY *aux = Opt_stab()->Aux_stab_entry(v->Aux_id());
  if (aux->Is_dedicated_preg() || ! aux->Is_real_var())
    return UINT64_MAX;
  // if a preg, Value_size does not give entire register size, so use 
  // Bits_in_type(MTYPE_I8)
  if (ST_class(Opt_stab()->Aux_stab_entry(v->Aux_id())->St()) == CLASS_PREG){
#ifdef TARG_ST
    //
    // Arthur: I am not sure where the Bits_in_type(preg_mtype) is
    //         different from Dsctyp() for this LDID ??? It breaks
    //         the Only_32_Bit_Ops processing because we allow PREGs
    //         of mtype I8/U8, etc. However, Bits_in_type(Max_Int_Mtype)
    //         returns 32 bits (max register size on the machine) 
    //         and breaks the logic. Besides, I wonder how it works
    //         when we have a I4I2LDID (is it possible with a PREG ?)
    //         and why would this routine return 32 bits instead of
    //         16 ?
    //
    //         I'll try to use Dsctyp() and see what happens ...
    //
    //         In any case, it is incorrect for 40 bit types and
    //         Pointer_Mtype.
    //
    // [CG]: The above comment does not work, commented it out:
    //return Bits_in_type(v->Dsctyp());
    
    // Indeed we may have different types of preg. for instance
    // MTYPE_I8 is valid on 32 machines before lowering.
    // Thus on a 32 bit machine with 64 bits emulation we may have
    // preg of underlying size MTYPE_I4 or MTYPE_I8. In this case
    // the underlying size of the preg is encoded in its type.
    // This function must always return the underlying preg size
    // and not for instance 16 bits on a LDIDI4I2.
    // Max_Int_Mtype does not work for 64 bits preg as it
    // is set to MTYPE_I4 on 32 machines.
    // Thus we take the size of the PREG symbol type which is
    // always set to the underlying register size or 
    // emulated register size of 64 bits.
    return Bits_in_type(TY_mtype(ST_type(Opt_stab()->Aux_stab_entry(v->Aux_id())->St())));
#else
    return Bits_in_type(MTYPE_I8);
#endif
  }
  if (aux->Byte_size() != 0)
    return Bitmask_of_size(aux->Byte_size() * 8);
  return Bits_in_type(v->Dsctyp());
}

// ====================================================================
// Mark_entire_var_live - by following use-def edges; cr must be a CK_VAR node.
// ====================================================================
void
BITWISE_DCE::Mark_entire_var_live(CODEREP *cr, BOOL stmt_visit)
{
  if (Tracing())
    fprintf(TFile, "Mark_entire_var_live(cr%d,%d)\n",
	    cr->Coderep_id(), stmt_visit);

  if (stmt_visit)
    IncUsecnt(cr);

  if (! More_bits_live(cr, Bits_in_var(cr)))
    return;

  stmt_visit = _copy_propagate && (Livebits(cr) == 0);

  Union_livebits(cr, Bits_in_var(cr));
  if (cr->Is_flag_set(CF_DEF_BY_PHI)) {
    PHI_NODE *phi = cr->Defphi();
    PHI_OPND_ITER phi_opnd_iter(phi);
    CODEREP *opnd;
    FOR_ALL_ELEM(opnd, phi_opnd_iter, Init()) {
      if (! opnd->Is_flag_set(CF_IS_ZERO_VERSION))
	Mark_entire_var_live(opnd, stmt_visit);
    }
  }
  else if (cr->Defstmt())	   // defstmt is NULL if volatile
    Mark_stmt_live(cr->Defstmt()); // def by chi or real stid
}

// ====================================================================
// Mark_var_bits_live - by following use-def edges; cr must be a CK_VAR node.
// The bits in live_bits can be more than the variable size due to sign- or
// zero extension of the load
// ====================================================================
void
BITWISE_DCE::Mark_var_bits_live(CODEREP *cr, UINT64 live_bits,
				BOOL stmt_visit)
{
  if (Tracing())
    fprintf(TFile, "Mark_var_bits_live(cr%d,%d)\n",
	    cr->Coderep_id(), stmt_visit);

  live_bits &= Bits_in_var(cr); // trim away bits beyond variable's size

  if (stmt_visit)
    IncUsecnt(cr);

  if (! More_bits_live(cr, live_bits))
    return;

  stmt_visit = _copy_propagate && (Livebits(cr) == 0);

  Union_livebits(cr, live_bits);
  if (cr->Is_flag_set(CF_DEF_BY_PHI)) {
    PHI_NODE *phi = cr->Defphi();
    PHI_OPND_ITER phi_opnd_iter(phi);
    CODEREP *opnd;
    FOR_ALL_ELEM(opnd, phi_opnd_iter, Init()) {
      if (! opnd->Is_flag_set(CF_IS_ZERO_VERSION))
	Mark_var_bits_live(opnd, live_bits, stmt_visit);
    }
  }
  else if (cr->Is_flag_set(CF_DEF_BY_CHI)) {
    if (! cr->Is_flag_set(CF_IS_ZERO_VERSION))
      Mark_stmt_live(cr->Defstmt());
  }
  else { // def is real stid
    if (cr->Defstmt()) {       	    // defstmt is NULL if volatile
#if defined( KEY) && !defined(TARG_ST) // bug 2666
      Mark_tree_bits_live(cr->Defstmt()->Rhs(), live_bits, stmt_visit);
#else
      Mark_tree_bits_live(cr->Defstmt()->Rhs(), live_bits, FALSE);
#endif
    }
//  Make_bb_live(cr->Defstmt()->Bb()); not needed because all BBs already live
  }
}

// ====================================================================
// Mark_tree_bits_live - propagate the live bits top-down in the expression
// tree. When at the variable node, propagate to its def. If data type is
// any floating-point type, propagate all 64 bits live (it may be more than
// 64-bits wide, but that is not a problem).
// ====================================================================
void
BITWISE_DCE::Mark_tree_bits_live(CODEREP *cr, UINT64 live_bits,
				 BOOL stmt_visit)
{
  UINT64 new_livebits;
  if (Tracing())
    fprintf(TFile, "Mark_tree_bits_live(cr%d,%" SCNd64 ",%d)\n",
	    cr->Coderep_id(), live_bits, stmt_visit);

  if (stmt_visit && cr->Kind() != CK_VAR) // Avoid redundant VAR IncUsecnt
    if (Usecnt(cr) < 2)
      IncUsecnt(cr);
    else
      stmt_visit = FALSE;

  BOOL visit_all = (stmt_visit || Livebits(cr) == 0);

  switch (cr->Kind()) {
  case CK_CONST:
  case CK_RCONST:
  case CK_LDA:
    Union_livebits(cr, live_bits);
    return;

  case CK_VAR:
    new_livebits = live_bits & Bits_in_var(cr);
#ifdef TARG_ST
    if ((MTYPE_signed(cr->Dsctyp()) || MTYPE_size_min(cr->Dsctyp()) == 32) &&
#else
    if ((MTYPE_signed(cr->Dsctyp()) || MTYPE_size_min(cr->Dsctyp()) == 32) &&
#endif
	(live_bits >> MTYPE_size_min(cr->Dsctyp())) != 0) {
      // make the sign bit live
      new_livebits |= (1 << (MTYPE_size_min(cr->Dsctyp()) - 1)); 
    }

    if (Bits_in_var(cr) == new_livebits) // new_livebits cover entire variable?
      Mark_entire_var_live(cr, stmt_visit);
    else
      Mark_var_bits_live(cr, new_livebits, stmt_visit);
    return;

  case CK_IVAR:
    if (cr->Opr() != OPR_PARM) {
      if (visit_all) {
        Mark_tree_bits_live(cr->Ilod_base(), Bits_in_type(Pointer_type),
			    stmt_visit);
        if (cr->Opr() == OPR_MLOAD)
          Mark_tree_bits_live(cr->Mload_size(), 
			      Bits_in_coderep_result(cr->Mload_size()),
			      stmt_visit);
#ifndef TARG_ST
        else if (cr->Opr() == OPR_ILOADX)
          Mark_tree_bits_live(cr->Index(), 
			      Bits_in_coderep_result(cr->Index()),
			      stmt_visit);
#endif
        MU_NODE *mnode = cr->Ivar_mu_node();
        if (mnode && ! mnode->OPND()->Is_flag_set(CF_IS_ZERO_VERSION))
	  Mark_entire_var_live(mnode->OPND(), stmt_visit);
      }

      new_livebits = live_bits & Bits_in_type(cr->Dsctyp());
#ifdef TARG_ST
      if ((MTYPE_signed(cr->Dsctyp()) || MTYPE_size_min(cr->Dsctyp()) == 32) &&
#else
      if ((MTYPE_signed(cr->Dsctyp()) || MTYPE_size_min(cr->Dsctyp()) == 32) &&
#endif
          (live_bits >> MTYPE_size_min(cr->Dsctyp())) != 0) {
        // make the sign bit live
        new_livebits |= (1 << (MTYPE_size_min(cr->Dsctyp()) - 1)); 
      }

      if (More_bits_live(cr, new_livebits))
	Union_livebits(cr, new_livebits);
      return;
    }
    else { // live_bits must be UINT64_MAX for parm nodes
      live_bits &= Bits_in_type(cr->Dtyp()); // trim away bits beyond parm size

      if (! stmt_visit && ! More_bits_live(cr, live_bits))
	return;

      Union_livebits(cr, live_bits);
      Mark_tree_bits_live(cr->Ilod_base(), live_bits, stmt_visit);
      MU_NODE *mnode = cr->Ivar_mu_node();
      if (mnode && ! mnode->OPND()->Is_flag_set(CF_IS_ZERO_VERSION))
        Mark_entire_var_live(mnode->OPND(), stmt_visit);
      return;
    }

  case CK_OP: {
    INT32 i;
    OPERATOR opr = cr->Opr();

    // first, trim away bits beyond size of result
    switch (opr) {
    case OPR_EQ: case OPR_NE:
    case OPR_GE: case OPR_GT: case OPR_LE: case OPR_LT:
    case OPR_LNOT:
    case OPR_LAND: case OPR_LIOR:
      live_bits &= 1;
      break;
    default: ;
    }

    if (! stmt_visit && ! More_bits_live(cr, live_bits))
      return;

    Union_livebits(cr, live_bits);
    MTYPE dtyp = cr->Dtyp();
    MTYPE dsctyp = (cr->Dsctyp() == MTYPE_V) ? dtyp : cr->Dsctyp();
    // our implementation of divide looks at all 64 bits even for 32-bit divide
    if (Only_Unsigned_64_Bit_Ops &&
        (opr == OPR_DIV || opr == OPR_DIVREM || opr == OPR_MOD || opr == OPR_REM))
      dsctyp = Mtype_TransferSize(MTYPE_A8, dsctyp);

    switch (opr) {

    // unary ops

    case OPR_CVTL: {
      new_livebits = Livebits(cr) & Bitmask_of_size(cr->Offset());
      if (MTYPE_signed(dtyp) &&
	  (Livebits(cr) >> cr->Offset()) != 0) {
	UINT64 sign_bit_mask = 1LL << (cr->Offset() - 1);
	new_livebits |= sign_bit_mask; // make only the most 
						   // significant bit live
      }
      Mark_tree_bits_live(cr->Opnd(0), new_livebits, stmt_visit);
      return;
    }

    case OPR_CVT:
      if (dsctyp == MTYPE_B)
        Mark_tree_bits_live(cr->Opnd(0), 1, stmt_visit);
      else if (MTYPE_is_integral(dtyp) && MTYPE_is_integral(dsctyp)) {
	new_livebits = Livebits(cr) & Bits_in_type(dtyp) & Bits_in_type(dsctyp);
        if ((dsctyp == MTYPE_I4 || MTYPE_size_min(dtyp) == 32) && 
	    (Livebits(cr) >> 32) != 0)
	  new_livebits |= (1 << 31);  // make the 31st bit live
        Mark_tree_bits_live(cr->Opnd(0), new_livebits, stmt_visit);
      }
      else if (visit_all)
	  Mark_tree_bits_live(cr->Opnd(0), Bits_in_type(dsctyp), stmt_visit);
      return;

    case OPR_NEG:
      Mark_tree_bits_live(cr->Opnd(0),
			  Bits_in_type(dsctyp) & Fill_lower_bits(Livebits(cr)),
			  stmt_visit);
      return;

    case OPR_EXTRACT_BITS: // modeled after OPR_CVTL
      new_livebits = Livebits(cr) & Bitmask_of_size(cr->Op_bit_size());
      if (MTYPE_signed(dtyp) &&
	  (Livebits(cr) >> cr->Op_bit_size()) != 0) {
	UINT64 sign_bit_mask = 1LL << (cr->Op_bit_size() - 1);
	new_livebits |= sign_bit_mask; // make only the most 
						   // significant bit live
      }
#if defined( KEY) && !defined(TARG_ST)
      if (Target_Byte_Sex == BIG_ENDIAN)
        Mark_tree_bits_live(cr->Opnd(0), new_livebits << 
	      (MTYPE_bit_size(dtyp) - cr->Op_bit_offset() - cr->Op_bit_size()),
			    stmt_visit);
      else
#endif
      Mark_tree_bits_live(cr->Opnd(0), new_livebits << cr->Op_bit_offset(),
			  stmt_visit);
      return;

    case OPR_PAREN:
    case OPR_BNOT: 
    case OPR_MINPART: case OPR_MAXPART:
      new_livebits = Bits_in_type(dsctyp) & Livebits(cr);
      if (MTYPE_size_min(dsctyp) == 32 && (Livebits(cr) >> 32) != 0)
	new_livebits |= (1 << 31);  // make the 31st bit live
      Mark_tree_bits_live(cr->Opnd(0), new_livebits, stmt_visit);
      return;

    case OPR_ABS:
    case OPR_LNOT:
    case OPR_RND: case OPR_TRUNC: case OPR_CEIL: case OPR_FLOOR:
    case OPR_SQRT: case OPR_RSQRT: case OPR_RECIP:
    case OPR_REALPART: case OPR_IMAGPART:
    case OPR_HIGHPART: case OPR_LOWPART:
    case OPR_TAS:
#if defined( KEY) && !defined(TARG_ST)
    case OPR_REPLICATE:
    case OPR_REDUCE_ADD:
    case OPR_REDUCE_MPY:
    case OPR_REDUCE_MAX:
    case OPR_REDUCE_MIN:
    case OPR_SHUFFLE:
    case OPR_ATOMIC_RSQRT:
#endif
      if (visit_all)
	Mark_tree_bits_live(cr->Opnd(0), Bits_in_type(dsctyp), stmt_visit);
      return;

    // binary ops

    case OPR_ADD: case OPR_SUB: case OPR_MPY:
      Mark_tree_bits_live(cr->Opnd(0), 
			  Bits_in_type(dsctyp) & Fill_lower_bits(Livebits(cr)),
			  stmt_visit);
      Mark_tree_bits_live(cr->Opnd(1), 
			  Bits_in_type(dsctyp) & Fill_lower_bits(Livebits(cr)),
			  stmt_visit);
      return;
#ifdef TARG_ST
       case OPR_BIOR: case OPR_BNOR:
#endif
    case OPR_BXOR:
      new_livebits = Livebits(cr) & Bits_in_type(dsctyp);
      if (MTYPE_size_min(dsctyp) == 32 && (Livebits(cr) >> 32) != 0)
	new_livebits |= (1 << 31);  // make the 31st bit live
      Mark_tree_bits_live(cr->Opnd(0), new_livebits, stmt_visit);
      Mark_tree_bits_live(cr->Opnd(1), new_livebits, stmt_visit);
      return;

    case OPR_XMPY: case OPR_HIGHMPY:
    case OPR_DIV: case OPR_MOD: case OPR_REM: case OPR_DIVREM:
    case OPR_MAX: case OPR_MIN: case OPR_MINMAX:
    case OPR_EQ: case OPR_NE:
    case OPR_GE: case OPR_GT: case OPR_LE: case OPR_LT:
    case OPR_LAND: case OPR_LIOR:
    case OPR_COMPLEX:
      if (visit_all) {
	Mark_tree_bits_live(cr->Opnd(0), Bits_in_type(dsctyp), stmt_visit);
	Mark_tree_bits_live(cr->Opnd(1), Bits_in_type(dsctyp), stmt_visit);
      }
      return;
#ifndef TARG_ST
    case OPR_BIOR: case OPR_BNOR: 
      new_livebits = Livebits(cr) & Bits_in_type(dsctyp);
      if (MTYPE_size_min(dsctyp) == 32 && (Livebits(cr) >> 32) != 0)
	new_livebits |= (1 << 31);  // make the 31st bit live
      if (cr->Opnd(0)->Kind() == CK_CONST) 
        Mark_tree_bits_live(cr->Opnd(1), new_livebits &
			    (~cr->Opnd(0)->Const_val()), stmt_visit);
      else Mark_tree_bits_live(cr->Opnd(1), new_livebits, stmt_visit);
      if (cr->Opnd(1)->Kind() == CK_CONST) 
        Mark_tree_bits_live(cr->Opnd(0), new_livebits &
			    (~cr->Opnd(1)->Const_val()), stmt_visit);
      else Mark_tree_bits_live(cr->Opnd(0), new_livebits, stmt_visit);
      return;
#endif
    case OPR_BAND: 
      new_livebits = Livebits(cr) & Bits_in_type(dsctyp);
      if (MTYPE_size_min(dsctyp) == 32 && (Livebits(cr) >> 32) != 0)
	new_livebits |= (1 << 31);  // make the 31st bit live
      if (cr->Opnd(0)->Kind() == CK_CONST) 
        Mark_tree_bits_live(cr->Opnd(1), new_livebits &
			    cr->Opnd(0)->Const_val(), stmt_visit);
      else Mark_tree_bits_live(cr->Opnd(1), new_livebits, stmt_visit);
      if (cr->Opnd(1)->Kind() == CK_CONST) 
        Mark_tree_bits_live(cr->Opnd(0), new_livebits &
			    cr->Opnd(1)->Const_val(), stmt_visit);
      else Mark_tree_bits_live(cr->Opnd(0), new_livebits, stmt_visit);
      return;
#ifndef TARG_ST
    case OPR_RROTATE:
      Mark_tree_bits_live(cr->Opnd(1), Bits_in_type(dsctyp), stmt_visit);
      new_livebits = Livebits(cr) & Bits_in_type(dtyp);
      Mark_tree_bits_live(cr->Opnd(0), new_livebits, stmt_visit);
      return;
#endif
#ifdef TARG_ST
    case OPR_ASHR: case OPR_LSHR:
      Mark_tree_bits_live(cr->Opnd(1), Bits_in_type(dsctyp), stmt_visit);
      if (cr->Opnd(1)->Kind() == CK_CONST) {
        INT64 shift_amt = cr->Opnd(1)->Const_val();
#ifdef TARG_MIPS
        if (MTYPE_size_min(dtyp) < MTYPE_size_min(MTYPE_U8))
	  shift_amt = 31 & cr->Opnd(1)->Const_val(); // use lower order 5 bits
#elif TARG_IA64
        if ((shift_amt < 0) || (shift_amt >= MTYPE_size_min(dtyp))) shift_amt = MTYPE_size_min(dtyp) -1;
#endif
        Mark_tree_bits_live(cr->Opnd(0),
		      (Bits_in_type(dsctyp) << shift_amt) &
		      Bits_in_type(dsctyp), stmt_visit);
      }
      else Mark_tree_bits_live(cr->Opnd(0), Bits_in_type(dsctyp), stmt_visit);
      return;
#else
    case OPR_LSHR:
      Mark_tree_bits_live(cr->Opnd(1), Bits_in_type(dsctyp), stmt_visit);
      if (cr->Opnd(1)->Kind() == CK_CONST) {
        INT64 shift_amt = cr->Opnd(1)->Const_val();
#if defined(TARG_MIPS) || defined(TARG_X8664)
        if (MTYPE_size_min(dtyp) < MTYPE_size_min(MTYPE_U8))
	  shift_amt = 31 & cr->Opnd(1)->Const_val(); // use lower order 5 bits
#elif TARG_IA64
        if ((shift_amt < 0) || (shift_amt >= MTYPE_size_min(dtyp))) shift_amt = MTYPE_size_min(dtyp) -1;
#endif
        Mark_tree_bits_live(cr->Opnd(0),
		      ((Bits_in_type(dsctyp) & live_bits) << shift_amt) &
		      Bits_in_type(dsctyp), stmt_visit);
      }
      else Mark_tree_bits_live(cr->Opnd(0), Bits_in_type(dsctyp), stmt_visit);
      return;
  
    case OPR_ASHR: 
      Mark_tree_bits_live(cr->Opnd(1), Bits_in_type(dsctyp), stmt_visit);
      if (cr->Opnd(1)->Kind() == CK_CONST) {
        INT64 shift_amt = cr->Opnd(1)->Const_val();
#if defined(TARG_MIPS) || defined(TARG_X8664)
        if (MTYPE_size_min(dtyp) < MTYPE_size_min(MTYPE_U8))
	  shift_amt = 31 & cr->Opnd(1)->Const_val(); // use lower order 5 bits
#elif TARG_IA64
        if ((shift_amt < 0) || (shift_amt >= MTYPE_size_min(dtyp))) shift_amt = MTYPE_size_min(dtyp) -1;
#endif
#ifdef KEY // need to do extra work to determine if the sign bit is live
        UINT64 sign_livebits;
	if (MTYPE_size_min(dtyp) < MTYPE_size_min(MTYPE_U8)) {
	  if (shift_amt <= 31 && (live_bits >> (31 - shift_amt)))
	    sign_livebits = 0x10000000;
	  else sign_livebits = 0;
	}
	else {
	  if (shift_amt <= 63 && (live_bits >> (63 - shift_amt)))
	    sign_livebits = 0x1000000000000000ULL;
	  else sign_livebits = 0;
	}
#endif
        Mark_tree_bits_live(cr->Opnd(0),
		      ((Bits_in_type(dsctyp) & live_bits) << shift_amt) &
		      Bits_in_type(dsctyp) 
#ifdef KEY
		      | sign_livebits
#endif
		      , stmt_visit);
      }
      else Mark_tree_bits_live(cr->Opnd(0), Bits_in_type(dsctyp), stmt_visit);
      return;
#endif 
    case OPR_SHL:
      Mark_tree_bits_live(cr->Opnd(1), Bits_in_type(dsctyp), stmt_visit);
      if (cr->Opnd(1)->Kind() == CK_CONST) {
        INT64 shift_amt = cr->Opnd(1)->Const_val();
        UINT64 bit_mask = Bits_in_type(dsctyp);
#if TARG_IA64
        if ((shift_amt < 0) || (shift_amt > MTYPE_size_min(dtyp))) bit_mask = 0;
#endif
	Mark_tree_bits_live(cr->Opnd(0),
		      ((bit_mask & live_bits) >> shift_amt) & bit_mask,
		      stmt_visit);
      }
      else Mark_tree_bits_live(cr->Opnd(0), Bits_in_type(dsctyp), stmt_visit);
      return;

    case OPR_COMPOSE_BITS:
#if defined( KEY) && !defined(TARG_ST)
      if (Target_Byte_Sex == BIG_ENDIAN)
        new_livebits = Livebits(cr) & 
		~(Bitmask_of_size(cr->Op_bit_size()) << 
	      (MTYPE_bit_size(dtyp) - cr->Op_bit_offset() - cr->Op_bit_size()));
      else
#endif
      new_livebits = Livebits(cr) & 
		~(Bitmask_of_size(cr->Op_bit_size()) << cr->Op_bit_offset());
      Mark_tree_bits_live(cr->Opnd(0), new_livebits, stmt_visit);
#if defined( KEY) && !defined(TARG_ST)
      if (Target_Byte_Sex == BIG_ENDIAN)
        new_livebits = (Livebits(cr) >> (MTYPE_bit_size(dtyp) - cr->Op_bit_offset() - cr->Op_bit_size())) & 
		       Bitmask_of_size(cr->Op_bit_size());
      else
#endif
      new_livebits = (Livebits(cr) >> cr->Op_bit_offset()) & 
		     Bitmask_of_size(cr->Op_bit_size());
      Mark_tree_bits_live(cr->Opnd(1), new_livebits, stmt_visit);
      return;

#ifdef TARG_ST
    case OPR_RROTATE: 
    case OPR_LROTATE: 
      Mark_tree_bits_live(cr->Opnd(0), Bits_in_type(dsctyp), stmt_visit);
      Mark_tree_bits_live(cr->Opnd(1), Bits_in_type(dsctyp), stmt_visit);
      return;
#endif
    // ternary ops

    // ternary and n-ary ops

    case OPR_SELECT:
      Mark_tree_bits_live(cr->Opnd(0), Bits_in_type(dsctyp), stmt_visit);
      Mark_tree_bits_live(cr->Opnd(1), Bits_in_type(dtyp) & Livebits(cr),
			  stmt_visit);
      Mark_tree_bits_live(cr->Opnd(2), Bits_in_type(dtyp) & Livebits(cr),
			  stmt_visit);
      return;

    case OPR_MADD: case OPR_MSUB:
    case OPR_NMADD: case OPR_NMSUB:
      if (visit_all)
	for (i = 0; i < cr->Kid_count(); i++) 
	  Mark_tree_bits_live(cr->Opnd(i), Bits_in_type(dsctyp), stmt_visit);
      return;

    case OPR_CALL: case OPR_ICALL: 
    case OPR_INTRINSIC_CALL: case OPR_INTRINSIC_OP:
    case OPR_FORWARD_BARRIER: case OPR_BACKWARD_BARRIER:
    case OPR_ALLOCA: case OPR_DEALLOCA:
    case OPR_ASM_STMT: case OPR_ASM_INPUT:
#if defined( KEY) && !defined(TARG_ST)
    case OPR_PURE_CALL_OP:
#endif
      if (visit_all) {
	for (i = 0; i < cr->Kid_count(); i++) {
	  Mark_tree_bits_live(cr->Opnd(i), UINT64_MAX, stmt_visit);
	}
      }
      return;

#ifdef TARG_ST
    case OPR_SUBPART:
      if(visit_all)
	  Mark_tree_bits_live(cr->Opnd(0), UINT64_MAX, stmt_visit);
      return;
#endif
    default:
      Is_True(FALSE,
	      ("BITWISE_DCE::Mark_tree_bits_live: unexpected operator"));
    }
    Is_True(FALSE,
	    ("BITWISE_DCE::Mark_tree_bits_live: missing return statement"));
  }

  default:
    Is_True(FALSE,
	    ("BITWISE_DCE::Mark_tree_bits_live: unexpected kind 0x%x",
	     cr->Kind()));
  }
  Is_True(FALSE,
	  ("BITWISE_DCE::Mark_tree_bits_live: missing return statement"));
}

// ====================================================================
//  Mark_stmt_live - mark statement to be live. If it is an STID, should
//  be called only if marking entire bits live; the var's own live bits should
//  have been set by the caller.
// ====================================================================
void
BITWISE_DCE::Mark_stmt_live(STMTREP *stmt) 
{
  if (stmt->Live_stmt())
    return;
  stmt->Set_live_stmt();

  if (Tracing())
    fprintf(TFile, "Mark_stmt_live(Sid%d)\n", stmt->Stmt_id());

  OPERATOR opr = stmt->Opr();
  if (opr == OPR_PREFETCH)
    Mark_tree_bits_live(stmt->Rhs()->Ilod_base(), Bits_in_type(Pointer_type),
			_copy_propagate /*stmt_visit*/ );
  else if (opr == OPR_RETURN_VAL)
    Mark_tree_bits_live(stmt->Rhs(), Bits_in_type(stmt->Rtype()),
			_copy_propagate /*stmt_visit*/ );
  else if (! OPERATOR_is_store(opr)) {
    if (stmt->Rhs() != NULL)
      Mark_tree_bits_live(stmt->Rhs(), Bits_in_coderep_result(stmt->Rhs()),
			  _copy_propagate /*stmt_visit*/ );
  }
  else if (opr == OPR_STID &&
	   ST_class(Opt_stab()->Aux_stab_entry(stmt->Lhs()->Aux_id())->St())
	   == CLASS_PREG) {
#if defined( KEY) && !defined(TARG_ST) // bug 14605: special-case for preg moves 
    if (stmt->Rhs()->Kind() == CK_VAR &&
	ST_class(Opt_stab()->Aux_stab_entry(stmt->Rhs()->Aux_id())->St())
	   == CLASS_PREG)
      Mark_tree_bits_live(stmt->Rhs(), Livebits(stmt->Lhs()),
			  _copy_propagate /*stmt_visit*/ );
    else
#endif
    Mark_tree_bits_live(stmt->Rhs(), Bits_in_coderep_result(stmt->Rhs()),
			_copy_propagate /*stmt_visit*/ );
  }
  else {
    switch (opr) {
#ifndef TARG_ST
    case OPR_ISTOREX:
#endif
    case OPR_MSTORE:
      if (opr == OPR_MSTORE)
	Mark_tree_bits_live(stmt->Lhs()->Mstore_size(), 
			    Bits_in_coderep_result(stmt->Lhs()->Mstore_size()),
			    _copy_propagate /*stmt_visit*/ );
      else
	Mark_tree_bits_live(stmt->Lhs()->Index(), 
			    Bits_in_coderep_result(stmt->Lhs()->Index()),
			    _copy_propagate /*stmt_visit*/ );
      // fall thru
    case OPR_ISTORE:
#ifdef TARG_ST
      //
      // Arthur: IA64 does not handle these because it gets replaced
      //         by EXTRACT_BITS/COMPOSE_BITS thing
      //
    case OPR_ISTBITS:
#endif
      Mark_tree_bits_live(stmt->Lhs()->Istr_base(), Bits_in_type(Pointer_type),
			  _copy_propagate /*stmt_visit*/ );
      // fall thru
    case OPR_STID:
#ifdef TARG_ST
      //
      // Arthur: IA64 does not handle these because it gets replaced
      //         by EXTRACT_BITS/COMPOSE_BITS thing
      //
    case OPR_STBITS:
#endif
      if (opr != OPR_MSTORE) {
        // a store to memory can cause truncation
        Mark_tree_bits_live(stmt->Rhs(), Bits_in_coderep_result(stmt->Rhs()) &
			                 Bits_in_type(stmt->Lhs()->Dsctyp()),
			    _copy_propagate /*stmt_visit*/ );
      }
      else Mark_tree_bits_live(stmt->Rhs(), UINT64_MAX,
			       _copy_propagate /*stmt_visit*/);
      break;
    default: 
      Is_True(FALSE, ("BITWISE_DCE::Mark_stmt_live: unexpected store stmt"));
    }
  }

  if (stmt->Has_mu()) {
    MU_LIST *mu_list = stmt->Mu_list();
    if ( mu_list != NULL ) {
      MU_LIST_ITER mu_iter;
      MU_NODE *mnode;
      FOR_ALL_NODE( mnode, mu_iter, Init(mu_list) ) {
	if (mnode->OPND()->Is_flag_set(CF_IS_ZERO_VERSION))
	  continue;
	Mark_entire_var_live(mnode->OPND(), _copy_propagate /*stmt_visit*/ );
      }
    }
  }

  if (stmt->Has_chi()) {
    CHI_LIST_ITER chi_iter;
    CHI_NODE *cnode;
    CHI_LIST *chi_list = stmt->Chi_list();
    FOR_ALL_NODE( cnode, chi_iter, Init(chi_list)) {
      if (! cnode->Live())
	continue;
      if (cnode->OPND()->Is_flag_set(CF_IS_ZERO_VERSION))
        continue;
      Mark_entire_var_live(cnode->OPND(), _copy_propagate /*stmt_visit*/ );
    }
  }

//Make_bb_live(stmt->Bb()); not needed because all BBs already made live 
}

// ====================================================================
// Find_and_mark_cd_branch_live - a live statement is control-dependent on
// this bb. Find and mark the branch statement live.  This routine is
// recursive so as to exhaustively go thru the iterated post-dominance
// frontiers.
// ====================================================================
void
BITWISE_DCE::Find_and_mark_cd_branch_live(BB_NODE *bb)
{
  if (Cd_bbs()->MemberP(bb))	// already done before?
    return;
  Cd_bbs()->Union1D(bb);

  STMTREP *stmt;  STMTREP_ITER       stmt_iter(bb->Stmtlist());
  // iterate through each statement (backward order)
  FOR_ALL_NODE_REVERSE(stmt, stmt_iter, Init()) {
    OPERATOR opr = stmt->Opr();
    if (opr == OPR_COMPGOTO || 
	opr == OPR_TRUEBR || opr == OPR_FALSEBR ||
	opr == OPR_REGION || opr == OPR_AGOTO) {
      Mark_stmt_live(stmt);
      return;
    }
  }
  Is_True(FALSE,
	  ("BITWISE_DCE::Find_and_mark_cd_branch_live: cannot find branch"));
  return;
}

// ====================================================================
// Make_bb_live - set the bit in the _live_bb bit vector to record that 
// some statement in this bb is found live; if this is called for the
// bb the first time, need to propagate liveness to BBs that it is
// control-dependent on.
// ====================================================================
void
BITWISE_DCE::Make_bb_live(BB_NODE *bb)
{
  if (Live_bbs()->MemberP(bb))	// already live
    return;
  Live_bbs()->Union1D(bb);

  if (bb->Kind() == BB_ENTRY && bb != Cfg()->Fake_entry_bb()) {
    STMTREP *entry_chi = bb->Stmtlist()->Head();
    Is_True(OPCODE_operator(entry_chi->Op()) == OPR_OPT_CHI, ("cannot find entry chi."));
    Mark_stmt_live(entry_chi);
  }

  // make operands of phi's whose results are zero version live
  PHI_NODE *phi;
  PHI_LIST_ITER phi_iter;
  FOR_ALL_ELEM(phi, phi_iter, Init(bb->Phi_list())) {
    if (phi->Live() &&
	(phi->RESULT()->Is_flag_set(CF_IS_ZERO_VERSION) ||
	 phi->RESULT()->Is_flag_set(CF_INCOMPLETE_USES))) {
      PHI_OPND_ITER phi_opnd_iter(phi);
      CODEREP *opnd;
      FOR_ALL_ELEM(opnd, phi_opnd_iter, Init()) {
        if (! opnd->Is_flag_set(CF_IS_ZERO_VERSION))
	  Mark_entire_var_live(opnd, _copy_propagate /*stmt_visit*/ );
      }
    }
  }

  // make statements without dependency in this bb live
  STMTREP_ITER stmt_iter(bb->Stmtlist());
  STMTREP *stmt;
  FOR_ALL_NODE(stmt, stmt_iter, Init()) {
    if (stmt->Live_stmt())
      continue;
    if ((stmt->Opr() == OPR_ISTORE || stmt->Opr() == OPR_MSTORE) &&
	stmt->Lhs()->Points_to(Opt_stab())->Restricted()) 
      Mark_stmt_live(stmt);
    else if (stmt->Volatile_stmt() || 
	     stmt->Opr() == OPR_STID && stmt->Lhs()->Is_var_volatile() ||
	     Operators_without_dependency(stmt->Opr()) ||
	     stmt->Has_zero_version_chi())
      Mark_stmt_live(stmt);
    else if (stmt->Opr() == OPR_STID && Opt_stab()->Is_varargs_func()) {
      CODEREP *lhs = stmt->Lhs();
      ST *s = Opt_stab()->St(lhs->Aux_id());
      CODEREP *rhs = stmt->Rhs();
      if (ST_sclass(s) == SCLASS_FORMAL && rhs->Kind() == CK_VAR &&
	  ST_class(Opt_stab()->St(rhs->Aux_id())) == CLASS_PREG &&
	  Preg_Is_Dedicated(rhs->Offset())) 
	// vararg parameters always need to be homed at PU entry; we don't know
	// if they are used
        Mark_stmt_live(stmt);
    }
#ifdef TARG_ST
    // Arthur: Should not remove STID of dedicated registers either
    // TODO: if it is right, share code with the above OPR_STID
    //
    else if (stmt->Opr() == OPR_STID) {
      CODEREP *lhs = stmt->Lhs();
      ST *s = Opt_stab()->St(lhs->Aux_id());
      if (ST_class(s) == CLASS_PREG && Preg_Is_Dedicated(lhs->Offset())) {
	Mark_stmt_live(stmt);
      }
    }
#endif
  }

  if (! bb->Willexit())
    return;

  // go through the post dominance frontiers of bb
  BB_NODE *bby;
  BB_NODE_SET_ITER bns_iter;
  FOR_ALL_ELEM (bby, bns_iter, Init(bb->Rcfg_dom_frontier())) 
    Find_and_mark_cd_branch_live(bby);

  // the above does not include the bb itself; include the bb itself if it
  // is among the predecessors
  BB_LIST_ITER bb_iter;
  FOR_ALL_ELEM (bby, bb_iter, Init(bb->Pred())) {
    if (bby == bb) {
      Find_and_mark_cd_branch_live(bb);
      break;
    }
  }
}

// ====================================================================
//  Find_and_mark_return_live - within the bb, find the return statement
//  and call Mark_stmt_live for it. The BBs post-dominated by the
//  fake exit bb are not guaranteed to have a return statement. So this routine
//  may NOT find the return statement.  This routine also find any STID to
//  dedicated pregs and mark it live in the same BB.  
// ====================================================================
void
BITWISE_DCE::Find_and_mark_return_live(BB_NODE *bb)
{
  BOOL return_found = FALSE;
  STMTREP *stmt;
  STMTREP_ITER       stmt_iter(bb->Stmtlist());
  // iterate through each statement (backward order)
  FOR_ALL_NODE_REVERSE(stmt, stmt_iter, Init()) {
    if (stmt->Opr() == OPR_RETURN || 
	stmt->Opr() == OPR_RETURN_VAL ||
#if defined( KEY) && !defined(TARG_ST)
  	stmt->Opr() ==  OPR_GOTO_OUTER_BLOCK ||
#endif
	stmt->Opr() == OPR_REGION_EXIT) {
      return_found = TRUE;
      Mark_stmt_live(stmt);
      if (Tracing())
	fprintf(TFile, "Return stmt at BB %" PRIdPTR "\n", bb->Id());
      if (stmt->Opr() == OPR_RETURN_VAL)
        break;
    }
    else if (! return_found && ! OPERATOR_is_not_executable(stmt->Opr()))
      return;  // this BB does not contain a return
    else if (stmt->Opr() == OPR_STID && 
	Opt_stab()->Aux_stab_entry(stmt->Lhs()->Aux_id())->Is_dedicated_preg())
      Mark_entire_var_live(stmt->Lhs(), FALSE);
  }
  return;
}

// ====================================================================
// Mark_willnotexit_stmts_live - We are in a region that does not reach
// a return statement.  Within this region, need to call Mark_stmt_live
// for all statements.
// ====================================================================
void
BITWISE_DCE::Mark_willnotexit_stmts_live(BB_NODE *bb)
{
  if (Tracing())
    fprintf(TFile, "Willnotexit BB %" PRIdPTR "\n", bb->Id());

  Cd_bbs()->Union1D(bb);

  STMTREP *stmt;
  STMTREP_ITER       stmt_iter(bb->Stmtlist());
  // iterate through each statement (backward order)
  FOR_ALL_NODE_REVERSE(stmt, stmt_iter, Init()) 
    Mark_stmt_live(stmt);

  // recursive call
  BB_NODE *pdom_bb;
  BB_LIST_ITER pdom_bb_iter;
  FOR_ALL_ELEM(pdom_bb, pdom_bb_iter, Init(bb->Pdom_bbs())) {
    if (! pdom_bb->Willexit())
      Mark_willnotexit_stmts_live(pdom_bb);	
  }
}

// ====================================================================
// Redundant_cvtl - check whether the CVTL represented by the parameters
// sign_xtd and to_bit/from_bit is redundant by looking at its operand opnd.
// If it is a preg use, follow the use def edge.  Right now, only doing the 
// simplest cases.
// ====================================================================
BOOL
BITWISE_DCE::Redundant_cvtl(BOOL sign_xtd, INT32 to_bit, INT32 from_bit, 
			    CODEREP *opnd)
{
  Is_True(to_bit == 32 || to_bit == 64,
	  ("BITWISE_DCE::Redundant_cvtl: illegal to_bit"));
  Is_True(from_bit != 0,
	  ("BITWISE_DCE::Redundant_cvtl: illegal from_bit"));
  MTYPE dtyp = opnd->Dtyp();
  if (dtyp == MTYPE_B)
    return ! sign_xtd || from_bit != 1;
  if (! MTYPE_is_integral(dtyp))
    return FALSE;

  switch (opnd->Kind()) {
  case CK_CONST:
    if (Split_64_Bit_Int_Ops && 
	MTYPE_bit_size(opnd->Dtyp()) <= 32 &&
	to_bit > 32)
      return FALSE;
    // return true if applying the cvtl to the int const yields the same value
    if (sign_xtd) {
      if (to_bit == 64) {
        INT64 sval64 = opnd->Const_val();
        sval64 = sval64 << (64 - from_bit) >> (64 - from_bit);
	return sval64 == opnd->Const_val();
      }
      else {
        INT32 sval32 = opnd->Const_val();
	return sval32 == (sval32 << (32 - from_bit) >> (32 - from_bit));
      }
    }
    else {
      if (to_bit == 64) {
	UINT64 uval64 = opnd->Const_val();
        uval64 = uval64 << (64 - from_bit) >> (64 - from_bit);
	return uval64 == opnd->Const_val();
      }
      else {
        UINT32 uval32 = opnd->Const_val();
	return uval32 == (uval32 << (32 - from_bit) >> (32 - from_bit));
      }
    }

  case CK_RCONST:
  case CK_LDA:
    return FALSE;

  case CK_VAR: {
    AUX_STAB_ENTRY *aux = Opt_stab()->Aux_stab_entry(opnd->Aux_id());
    if (aux->Is_dedicated_preg())
      return FALSE;
    if (ST_class(aux->St()) == CLASS_PREG) {
      // follow use-def edge
      if (opnd->Is_flag_set(CF_DEF_BY_CHI)) {
	Is_True(opnd->Defstmt()->Opr() == OPR_OPT_CHI,
		("BITWISE_DCE::Redundant_cvtl: preg cannot be defined by chi"));
	return FALSE;
      }
      else if (opnd->Is_flag_set(CF_DEF_BY_PHI)) {
	// could also apply to each phi operand, but need to prevent infinite
	// loop; not doing this for now.
	return FALSE;
      }
#ifdef TARG_X8664 // suppress this optimization since not yet in sync with 
      		  // CG about assumptions for sign extension (bugs 1046, 7228)
      else if (MTYPE_size_min(dtyp) == 32)
	return FALSE;
#endif
      else return Redundant_cvtl(sign_xtd, to_bit, from_bit, opnd->Defstmt()->Rhs());
    }
    // load from memory
    if (Split_64_Bit_Int_Ops && to_bit == 64)
      return FALSE;
#ifdef TARG_X8664
    if (MTYPE_size_min(opnd->Dsctyp()) < 32 && to_bit == 64) 
      return !sign_xtd && !opnd->Is_sign_extd() && 
	     from_bit >= MTYPE_size_min(opnd->Dsctyp());
#endif
    if (sign_xtd == opnd->Is_sign_extd())
      return from_bit >= MTYPE_size_min(opnd->Dsctyp());
    return ! opnd->Is_sign_extd() && from_bit > MTYPE_size_min(opnd->Dsctyp());
    }

  case CK_IVAR:
    if (opnd->Opr() == OPR_PARM)
      return FALSE;
    if (opnd->Opr() == OPR_MLOAD)
      return FALSE;
    if (Split_64_Bit_Int_Ops && to_bit == 64)
      return FALSE;
#ifdef TARG_X8664
    if (MTYPE_size_min(opnd->Dsctyp()) < 32 && to_bit == 64)
      return !sign_xtd && !opnd->Is_sign_extd() &&
	     from_bit >= MTYPE_size_min(opnd->Dsctyp());
#endif
    if (sign_xtd == opnd->Is_sign_extd())
      return from_bit >= MTYPE_size_min(opnd->Dsctyp());
    return ! opnd->Is_sign_extd() && from_bit > MTYPE_size_min(opnd->Dsctyp());

  case CK_OP: {
    MTYPE dsctyp;
    OPERATOR opr = opnd->Opr();
    switch(opr) {

    case OPR_CVTL:
#if defined( KEY) && !defined(TARG_ST)
      // if the opnd is newly created, the usecnt should be 0.
      // Therefore, it doesn't contain any livebits information. In addition,
      // since it is new cr, it will not be marked as dead by bdce in early phase.
      // The bug 2656 will not expose for this case.
      if (opnd->Usecnt() > 0  && 
          (Livebits(opnd) & ~Bitmask_of_size(opnd->Offset())) == 0)
	return FALSE; // this current node will be deleted any way (bug 2656)
#endif
      if (MTYPE_is_signed(dtyp) == sign_xtd) {
#ifndef TARG_X8664
	return from_bit >= opnd->Offset();
#else
	if (! MTYPE_is_signed(dtyp))
	  return from_bit >= opnd->Offset();
	else { // bug 2838: I4CVTL will not sign-extend the highest 32 bits
	  INT32 cvtl_to_bit = MTYPE_size_min(dtyp);
	  return from_bit >= opnd->Offset() && to_bit <= cvtl_to_bit;
	}
#endif
      }
      return ! MTYPE_is_signed(dtyp) && from_bit > opnd->Offset();

    case OPR_CVT:
      dsctyp = opnd->Dsctyp();
      if (! MTYPE_is_integral(dsctyp) ||
	  MTYPE_size_min(dtyp) <= MTYPE_size_min(dsctyp))
	return FALSE;
#if defined( KEY) && !defined(TARG_ST)
      if (MTYPE_size_min(dtyp) > MTYPE_size_min(dsctyp) &&
          opnd->Usecnt() > 0 && 
	  (Livebits(opnd) & ~Bits_in_type(dsctyp)) == 0)
	return FALSE; // this current node will be deleted any way (bug 2656)
#endif
      return MTYPE_is_signed(dtyp) == sign_xtd && 
	     from_bit >= MTYPE_size_min(dsctyp);

    case OPR_EQ: case OPR_NE:
    case OPR_GE: case OPR_GT: case OPR_LE: case OPR_LT:
    case OPR_LNOT:
    case OPR_LAND: case OPR_LIOR:
      return ! sign_xtd || from_bit != 1;
#if defined( KEY) && !defined(TARG_ST)
    case OPR_BAND: 
      { CODEREP *kopnd;
        if (sign_xtd)
	  return FALSE;
        if (opnd->Opnd(0)->Kind() == CK_CONST)
	  kopnd = opnd->Opnd(0);
	else if (opnd->Opnd(1)->Kind() == CK_CONST)
	  kopnd = opnd->Opnd(1);
	else return FALSE;
	UINT64 uval64 = kopnd->Const_val();
	return uval64 <= ((0x1ll << from_bit) - 1);
      }
#endif
#ifndef TARG_ST
    case OPR_ASHR:
      //       I4I4LDID 0 <2,1,a>
      //       I4INTCONST 24 (0x18)
      //     I4ASHR
      //   I4CVTL 8  <- reduntant CVTL
      if (opnd->Opnd(1)->Kind() == CK_CONST) {
        if (from_bit >= (MTYPE_size_min(dtyp) - opnd->Opnd(1)->Const_val()) &&
	    from_bit < MTYPE_size_min(dtyp) /* bug 14659 */) {
          return (MTYPE_signed(dtyp) == sign_xtd);
        }
      }
      return FALSE;
    case OPR_EXTRACT_BITS:
      //      U4U4LDID 72 <1,4,.preg_U4>
      //    U4EXTRACT_BITS <bofst:27 bsize:4>
      //  U4CVTL 8                         
      if (opnd->Op_bit_size() <= from_bit) {
	if (MTYPE_signed(dtyp) == sign_xtd)
	  return TRUE;
	if (opnd->Op_bit_size() < from_bit)
	  return ! MTYPE_signed(dtyp);
      }
      return FALSE;

#ifdef KEY // bug 15031
    case OPR_RROTATE:
      if (sign_xtd)
	return FALSE;
      if (from_bit >= MTYPE_bit_size(opnd->Dsctyp()))
	return Redundant_cvtl(sign_xtd, to_bit, from_bit, opnd->Opnd(0));
      return FALSE;
#endif
#endif
    default: ;
    }
    return FALSE;
    }

  default: ;
  }
  return FALSE; // dummy
}


#if defined( KEY) && !defined(TARG_ST) // bug 14903: do not let ILOAD disable propagation in BDCE
BOOL
CODEREP::Propagatable_in_bdce(OPT_STAB *sym) const
{
  switch (kind) {
  case CK_LDA: 
  case CK_CONST: 
  case CK_RCONST:
    return TRUE;
  case CK_VAR:
    {
      // check if it is volatile
      if (Is_var_volatile())
	return FALSE;
      // check if it is a physical register
      ST *s = sym->St(Aux_id());
      if ((ST_class(s) == CLASS_PREG && Preg_Is_Dedicated(Offset())))
	return FALSE;
      return TRUE;
    }
  case CK_IVAR: 
    if (Is_ivar_volatile())
      return FALSE;
    if (! Ilod_base()->Propagatable_in_bdce(sym))
      return FALSE;
    return TRUE;
  case CK_OP:
    if (OPCODE_is_volatile(Op()))
      return FALSE;
    for  (INT32 i = 0; i < Kid_count(); i++) {
      if (! Opnd(i)->Propagatable_in_bdce(sym))
	return FALSE;
    }
    if (! Op_can_be_propagated(Op(), sym->Phase())) 
      return FALSE;
    // Reference 644395 for situations when INTRINSIC_OP cannot be
    // copy propagated.
    if (Opr() == OPR_INTRINSIC_OP || Opr() == OPR_PURE_CALL_OP)
      return FALSE;
    return TRUE;
  }
  return FALSE;
}
#endif


// ====================================================================
// Copy_propagate - return the root of the propagated tree if the
// variable cr can be replaced by its definition; otherwise, return NULL.
// ====================================================================
CODEREP *
BITWISE_DCE::Copy_propagate(CODEREP *cr, STMTREP *use_stmt) {
  if (Usecnt(cr) != 1
      || cr->Is_flag_set((CR_FLAG)(CF_DEF_BY_PHI | CF_DEF_BY_CHI))
      || cr->Defstmt() == NULL) // volatile?
    return NULL;
  Is_True(cr->Defstmt()->Opr() == OPR_STID,
	  ("BITWISE_DCE::Copy_propagate: cr->Defstmt()->Opr() != OPR_STID"));

#if !defined( KEY) || defined(TARG_ST)
  // For now, just test if the definition immediately preceeds the use.
  if (use_stmt->Prev() != cr->Defstmt())
    return NULL;
#else
  // Relax to improve coverage
  if (use_stmt->Prev() != cr->Defstmt()) {
    if (WOPT_Enable_Bdceprop_Limit != -1 &&
        use_stmt->Bb()->Id() > WOPT_Enable_Bdceprop_Limit)
      return NULL;
    else if (! (Opt_stab()->Aux_stab_entry(cr->Aux_id())->EPRE_temp() &&
           	use_stmt->Bb() == cr->Defstmt()->Bb() &&
		!use_stmt->Iv_update() /* bug 10449 */) )
      return NULL;
  }
#endif

#if defined( KEY) && !defined(TARG_ST) // bug 8335: this may prevent CG from knowing what register name
	   // 		to use when handling the asm statemet
  if (use_stmt->Opr() == OPR_ASM_STMT &&
      ST_class(Opt_stab()->St(cr->Aux_id())) == CLASS_PREG)
    return NULL;
#endif

  CODEREP *new_expr = cr->Defstmt()->Rhs();
  Is_True(new_expr != NULL,
	  ("BITWISE_DCE::Copy_propagate: new_expr = NULL"));

#if defined( KEY) && !defined(TARG_ST) // bug 14903: do not let ILOAD disable propagation
  if (! new_expr->Propagatable_in_bdce(Opt_stab()))
#else
  if (! new_expr->Propagatable_for_ivr(Opt_stab()))
#endif
    return NULL;

  // More elaborate tests could use some of the following from opt_ivr.cxx:
  //   if (! (new_expr->Propagatable_for_ivr(Opt_stab())
  // 	 && new_expr->Propagatable_into_loop(loop)
  // 	 && new_expr->Propagatable_along_path(loop->Header()->Idom(),
  //                                               cr->Defbb()->Idom())))
  //     return NULL;
  // OR: Don't propagate into a loop
  // if (cr->Defstmt()->Bb()->Innermost() != loop) return NULL;
#ifdef TARG_ST
  // Arthur: do not propagate ASM_STMT outputs
  if ( new_expr->Kind() == CK_VAR && 
       ST_class(Opt_stab()->St(new_expr->Aux_id())) == CLASS_PREG &&
       ( new_expr->Offset() < 0 )) {
    return NULL;
  }

  // FdF 20071116: Old code cannot be removed if there are live chis
  // (codex #35792). This also prevent copy propagation, because this
  // would otherwise create non-conventional SSA.
  CHI_LIST_ITER chi_iter;
  CHI_NODE *chi;
  FOR_ALL_NODE(chi, chi_iter, Init(cr->Defstmt()->Chi_list())) {
    if (chi->Live() &&
	!chi->RESULT()->Is_flag_set(CF_IS_ZERO_VERSION) &&
	Livebits(chi->RESULT()) != 0) {
      return NULL;
    }
  }

  if (Tracing()) {
    fprintf(TFile, "BDCE copying:\n");
    cr->Defstmt()->Print(TFile);
    fprintf(TFile, "to:\n");
    use_stmt->Print(TFile);
  }
#endif
  // Propage copy and delete old code
  new_expr->IncUsecnt_rec();
  use_stmt->Bb()->Remove_stmtrep(cr->Defstmt());

  return new_expr;
}

// ====================================================================
// Delete_cvtls - return the new root of the tree if cvtl deletion
// results in a new tree; otherwise, return NULL.
// ====================================================================
CODEREP *
BITWISE_DCE::Delete_cvtls(CODEREP *cr, STMTREP *use_stmt)
{
#ifdef TARG_ST
  // Arthur: Includes both integer and pointer types
#endif

  if (MTYPE_is_integral(cr->Dtyp()) && Livebits(cr) == 0
#if defined( KEY) && !defined(TARG_ST) // bug 14142
      && ! cr->Has_volatile_content()
#endif
     ) { // a dead use
    // replace node by dummy 0 (otherwise, can cause live range overlap)
    cr->DecUsecnt_rec();
    return Htable()->Add_const(cr->Dtyp(), 0);
  }

  CODEREP *x, *x2;
  CODEREP *new_cr = Alloc_stack_cr(cr->Extra_ptrs_used());
  BOOL need_rehash;
  INT32 i;
  OPERATOR opr;
  switch (cr->Kind()) {
  case CK_CONST:
  case CK_RCONST:
  case CK_LDA:
    return NULL;
  case CK_VAR:
    return ( _copy_propagate ? Copy_propagate(cr, use_stmt) : NULL );
  case CK_IVAR:
    x = Delete_cvtls(cr->Ilod_base(), use_stmt);
    if (cr->Opr() == OPR_MLOAD)
      x2 = Delete_cvtls(cr->Mload_size(), use_stmt);
#ifndef TARG_ST
    else if (cr->Opr() == OPR_ILOADX)
      x2 = Delete_cvtls(cr->Index(), use_stmt);
#endif
    else x2 = NULL;
    if (x || x2) {  // need rehash
      new_cr->Copy(*cr);	
      new_cr->Set_istr_base(NULL);
      new_cr->Set_usecnt(0);
      if (x)
	new_cr->Set_ilod_base(x);
      if (x2)
	new_cr->Set_mload_size(x2);
      new_cr->Set_ivar_occ(cr->Ivar_occ());
      cr->DecUsecnt();
      return Htable()->Rehash(new_cr);
    }
    return NULL;

  case CK_OP:
    need_rehash = FALSE;
    new_cr->Copy(*cr);
    new_cr->Set_usecnt(0);
    // call recursively
#ifdef TARG_ST
    // FdF 24/05/2004 DDTS18034: On MPY operators, it is useful to
    // keep some CVTLs to generate 16x16 or 16x32 MUL operators.
    if (cr->Opr() != OPR_MPY ||
	((Livebits(cr) & ~0xffff) != 0))
#endif
    for (i = 0; i < cr->Kid_count(); i++) {
      x = Delete_cvtls(cr->Opnd(i), use_stmt);
      if (x) {
	need_rehash = TRUE;
	new_cr->Set_opnd(i, x);
      }
      else new_cr->Set_opnd(i, cr->Opnd(i));
    }
    // check if current node can be deleted
    opr = cr->Opr();
    if (opr == OPR_CVTL) {
      if (((Livebits(cr) & ~Bitmask_of_size(cr->Offset())) == 0) ||
	  Redundant_cvtl(MTYPE_is_signed(cr->Dtyp()), 
			 MTYPE_size_min(cr->Dtyp()), cr->Offset(), 
#ifdef TARG_ST //[CG] bug fix, must use new cr!
			 new_cr->Opnd(0))) {
	// delete the node
	cr->DecUsecnt();
	return new_cr->Opnd(0);
      }
#else
#ifdef KEY
			 x ? x : 
#endif
			 cr->Opnd(0))) {
	// delete the node
	cr->DecUsecnt();
	if (need_rehash)
	  return x;
	else return cr->Opnd(0);
      }
#endif
    }
    else if (opr == OPR_CVT) {
      MTYPE dtyp = cr->Dtyp();
      MTYPE dsctyp = cr->Dsctyp();
      if (dsctyp == MTYPE_B)
	; // CVT from MTYPE_B cannot be deleted
      else if (MTYPE_is_vector(dtyp) || MTYPE_is_vector(dsctyp))
	; // CVT involving SIMD types cannot be deleted (bug 14341)
      else if (MTYPE_is_integral(dtyp) && MTYPE_is_integral(dsctyp)) {
	if (MTYPE_size_min(dtyp) > MTYPE_size_min(dsctyp)) { // widening
          if (((Livebits(cr) & ~Bits_in_type(dsctyp)) == 0) ||
	      Redundant_cvtl(MTYPE_is_signed(dsctyp), 
			     MTYPE_size_min(dtyp), MTYPE_size_min(dsctyp), 
#ifdef TARG_ST //[CG] bug fix, must use new cr!
		new_cr->Opnd(0))) {
	      // delete the node
	      cr->DecUsecnt();
	      return new_cr->Opnd(0);
	    }
#else
#ifdef KEY
			     x ? x : 
#endif
			     cr->Opnd(0))) {
	    // delete the node
	    cr->DecUsecnt();
	    if (need_rehash)
	      return x;
	    else return cr->Opnd(0);
	  }
#endif
        }
#if !defined(TARG_MIPS) && !defined(TARG_X8664) // undeletable since garbage in high bits untolerable
        else { // truncation
	  if ((Livebits(cr) & ~Bitmask_of_size(MTYPE_size_min(dtyp))) == 0) {
#ifdef TARG_ST //[CG] bug fix, must use new cr!
	      // delete the node
	      cr->DecUsecnt();
	      return new_cr->Opnd(0);
#else
	    // delete the node
	    cr->DecUsecnt();
	    if (need_rehash)
	      return x;
	    else return cr->Opnd(0);
#endif
	  }
        }
#endif
      }
    }
#ifdef TARG_X8664
    else if (! Is_Target_64bit() && MTYPE_size_min(cr->Dtyp()) == 64 &&
	     MTYPE_is_integral(cr->Dtyp()) && 
	     (Livebits(cr) >> 32) == 0 &&
	     (opr == OPR_NEG || opr == OPR_BNOT || opr == OPR_LNOT ||
	      opr == OPR_ADD || opr == OPR_SUB || opr == OPR_MPY ||
	      opr == OPR_BAND || opr == OPR_BIOR || opr == OPR_BNOR ||
	      opr == OPR_BXOR || opr == OPR_LAND || opr == OPR_LIOR)) {
      // change the operation to 32-bit, which is good for 32-bit target
      cr->Set_dtyp(Mtype_TransferSize(MTYPE_I4, cr->Dtyp()));
      if (cr->Dsctyp() != MTYPE_V)
        cr->Set_dsctyp(Mtype_TransferSize(MTYPE_I4, cr->Dsctyp()));
      new_cr->Set_dtyp(Mtype_TransferSize(MTYPE_I4, new_cr->Dtyp()));
      if (new_cr->Dsctyp() != MTYPE_V)
        new_cr->Set_dsctyp(Mtype_TransferSize(MTYPE_I4, new_cr->Dsctyp()));
    }
#endif
    // can also apply to some BAND and BIOR with constants

    if (need_rehash) {
      cr->DecUsecnt();
      return Htable()->Rehash(new_cr);
    }
    return NULL;

  default: ;
  }
  return NULL; // dummy
}

// ====================================================================
// Delete_dead_nodes - go over all statements in the PU and delete dead
// statement nodes; for live statements, call Delete_cvtls for 
// expression trees.
// ====================================================================
void
BITWISE_DCE::Delete_dead_nodes(void)
{
  INT32 i;
  CFG_ITER cfg_iter(Cfg());
  BB_NODE *bb;
  // visit all blocks 
  FOR_ALL_NODE( bb, cfg_iter, Init() ) {
    // visit all statements; cannot use iterator because deleting at same time
    STMTREP *stmt, *nextstmt;
    for (stmt = bb->First_stmtrep();
	 stmt != NULL;
	 stmt = nextstmt) {
      nextstmt = stmt->Next();
      if (! stmt->Live_stmt() && 
	  stmt->Opr() == OPR_STID && Livebits(stmt->Lhs()) != 0)
	stmt->Set_live_stmt();
      if (! stmt->Live_stmt()) {
#if Is_True_On // verify that there is no live chi
        CHI_LIST_ITER chi_iter;
	CHI_NODE *chi;
        FOR_ALL_NODE(chi, chi_iter, Init(stmt->Chi_list())) 
	  Is_True(! chi->Live() ||
		  chi->RESULT()->Is_flag_set(CF_IS_ZERO_VERSION) ||
		  Livebits(chi->RESULT()) == 0,
		  ("BITWISE_DCE::Delete_dead_nodes: live chi in dead stmt"));
#endif // Is_True_On
	bb->Remove_stmtrep(stmt); // TODO: free up chi list?
	continue;
      }

      // statement is live
      OPERATOR opr = stmt->Opr();
      CODEREP *rhs = stmt->Rhs();
      CODEREP *x;
      if (OPERATOR_is_call(opr) || opr == OPR_ASM_STMT) {
	for (i = 0; i < rhs->Kid_count(); i++) {
	  x = Delete_cvtls(rhs->Opnd(i), stmt);
	  if (x)
	    rhs->Set_opnd(i, x);
	}
	continue;
      }
      if (rhs) {
	if (opr == OPR_PREFETCH) {
          x = Delete_cvtls(rhs->Ilod_base(), stmt);
	  if (x)
	    rhs->Set_ilod_base(x);
	}
	else {
          x = Delete_cvtls(rhs, stmt);
          if (x)
            stmt->Set_rhs(x);
	}
      }
      if (OPERATOR_is_store(opr)) {
	CODEREP *lhs = stmt->Lhs();
        switch (opr) {
        case OPR_MSTORE:
	  x = Delete_cvtls(lhs->Mstore_size(), stmt);
	  if (x)
	    lhs->Set_mstore_size(x);
	  // fall thru
        case OPR_ISTORE:
	  x = Delete_cvtls(lhs->Istr_base(), stmt);
	  if (x)
	    lhs->Set_istr_base(x);
	  break;
        default: ;
        }
      }
    }
  }
}

// ====================================================================
//  Bitwise_dce - Main routine for bitwise DCE; top level driver
// ====================================================================
void
BITWISE_DCE::Bitwise_dce(void)
{
  Initialize_stmts_dead();	// to initialize the SRF_LIVE_STMT bit to 0

  // make all BBs live
  CFG_ITER cfg_iter(Cfg());
  BB_NODE *bb;
  FOR_ALL_NODE( bb, cfg_iter, Init() ) 
    Make_bb_live(bb);

  if (Cfg()->Fake_exit_bb() == NULL) { // only 1 exit
    Find_and_mark_return_live(Cfg()->Exit_bb());
  }
  else { // multiple exit blocks
    BB_NODE *pdom_bb;
    BB_LIST_ITER pdom_bb_iter;
    FOR_ALL_ELEM(pdom_bb, pdom_bb_iter, Init(Cfg()->Exit_bb()->Pdom_bbs())) 
      if (pdom_bb->Willexit())
        Find_and_mark_return_live(pdom_bb);
      else Mark_willnotexit_stmts_live(pdom_bb);
  }

#if !defined( KEY) || defined(TARG_ST) // bug 8499
  // revisit STID stmts that were visited but not marked live
  if ( _copy_propagate ) {
    FOR_ALL_NODE( bb, cfg_iter, Init() ) {
      STMTREP_ITER stmt_iter(bb->Stmtlist());
      STMTREP *stmt;
      FOR_ALL_NODE(stmt, stmt_iter, Init()) {
	if (! stmt->Live_stmt() && stmt->Opr() == OPR_STID
	    && Livebits(stmt->Lhs()) != 0)
	  Mark_tree_bits_live(stmt->Rhs(), Livebits(stmt->Lhs()),
			      TRUE /*stmt_visit*/);
      }
    }
  }
#endif

  if (Tracing()) {
    Print_nodes_with_dead_bits(TFile);
    Print_node_usecnts(TFile);
  }

  // optimization pass
  Delete_dead_nodes();
}

// ====================================================================
//  Do_bitwise_dce - Set up the BITWISE_DCE environment and call it
// ====================================================================
void
COMP_UNIT::Do_bitwise_dce(BOOL copy_propagate)
{
  MEM_POOL bdce_pool;

  if ( Get_Trace(TP_GLOBOPT, DCE_DUMP_FLAG)) {
    fprintf( TFile, "%sBefore COMP_UNIT::Do_bitwise_dce\n%s",
             DBar, DBar );
    Cfg()->Print(TFile);
  }

  OPT_POOL_Initialize(&bdce_pool, "bitwise dce pool", FALSE, DCE_DUMP_FLAG);
  OPT_POOL_Push(&bdce_pool, DCE_DUMP_FLAG);

  {
    BITWISE_DCE bitwise_dce(Htable(), Opt_stab(), Cfg(), &bdce_pool,
			    copy_propagate);
    bitwise_dce.Bitwise_dce();
  }

  OPT_POOL_Pop(&bdce_pool, DCE_DUMP_FLAG);
  OPT_POOL_Delete(&bdce_pool, DCE_DUMP_FLAG);

  if ( Get_Trace(TP_GLOBOPT, DCE_DUMP_FLAG)) {
    fprintf( TFile, "%sAfter COMP_UNIT::Do_bitwise_dce\n%s",
             DBar, DBar );
    Cfg()->Print(TFile);
  }
}

// ====================================================================
// Print_nodes_with_dead_bits -
// ====================================================================
void
BITWISE_DCE::Print_nodes_with_dead_bits(FILE *fp) 
{
  CODEREP_ITER cr_iter;
  CODEREP *cr, *bucket;
  CODEMAP_ITER codemap_iter;

  fprintf(fp, "%sBitwise DCE found following nodes with dead bits in PU %s\n%s",
	  DBar, Cur_PU_Name, DBar);

  fprintf(fp, "- - - Default vsym is sym%1" PRIdPTR "\n", Opt_stab()->Default_vsym());
  fprintf(fp, "- - - Return vsym is sym%1" PRIdPTR "\n", Opt_stab()->Return_vsym());

  // expression nodes
  FOR_ALL_ELEM(bucket, codemap_iter, Init(Htable())) {
    FOR_ALL_NODE(cr, cr_iter, Init(bucket)) {
      if (cr->Dtyp() != MTYPE_UNKNOWN && // iload under prefetch has unknown dt
	  Livebits(cr) != Bits_in_coderep_result(cr)) {
	if (cr->Kind() == CK_OP) { // for boolean operators, print only if 0
	  switch (cr->Opr()) {
	  case OPR_EQ: case OPR_NE:
	  case OPR_GE: case OPR_GT: case OPR_LE: case OPR_LT:
	  case OPR_LNOT:
	  case OPR_LAND: case OPR_LIOR:
	    if (Livebits(cr) != 0)
	      continue;
	  default: ;
	  }
	}
	else if (cr->Kind() == CK_IVAR)
	  continue;
	Htable()->Print_CR(cr, fp);
	fprintf(fp, " has live bits 0x%" SCNx64 "\n", Livebits(cr));
      }
    }
  }

  // variable nodes
  AUX_ID i;
  AUX_STAB_ITER aux_stab_iter(Opt_stab());
  FOR_ALL_NODE(i, aux_stab_iter, Init()) {
    AUX_STAB_ENTRY *aux = Opt_stab()->Aux_stab_entry(i);
    FOR_ALL_NODE(cr, cr_iter, Init(aux->Cr_list())) {
      if (Livebits(cr) != Bits_in_var(cr) && 
	  ! cr->Is_flag_set(CF_IS_ZERO_VERSION) &&
	  ! Opt_stab()->Aux_stab_entry(cr->Aux_id())->Is_dedicated_preg()) {
	Htable()->Print_CR(cr, fp);
	fprintf(fp, " has live bits 0x%" SCNx64 "\n", Livebits(cr));
      }
    }
  }

  fprintf(fp, "%sBitwise DCE found following stmts dead in PU %s\n%s", 
	  DBar, Cur_PU_Name, DBar);
  CFG_ITER cfg_iter(Cfg());
  BB_NODE *bb;
  // visit all blocks (reached or not)
  FOR_ALL_NODE( bb, cfg_iter, Init() ) {
    // visit all statements
    STMTREP_ITER stmt_iter(bb->Stmtlist());
    STMTREP *stmt;
    FOR_ALL_NODE(stmt, stmt_iter, Init()) {
      if (stmt->Live_stmt())
	continue;
      if (stmt->Opr() == OPR_STID && Livebits(stmt->Lhs()) != 0)
	continue;
      stmt->Print(fp);
    }
  }
}

// ====================================================================
// Print_nodes_with_no_mult_uses -
// ====================================================================
void
BITWISE_DCE::Print_node_usecnts(FILE *fp)
{
  CODEREP_ITER cr_iter;
  CODEREP *cr, *bucket;
  CODEMAP_ITER codemap_iter;

  fprintf(fp, "%sBitwise DCE counted the following variable uses in PU %s\n%s",
	  DBar, Cur_PU_Name, DBar);

  // variable nodes
  AUX_ID i;
  AUX_STAB_ITER aux_stab_iter(Opt_stab());
  FOR_ALL_NODE(i, aux_stab_iter, Init()) {
    AUX_STAB_ENTRY *aux = Opt_stab()->Aux_stab_entry(i);
    FOR_ALL_NODE(cr, cr_iter, Init(aux->Cr_list())) {
      fprintf(fp, "cr%d has %u uses\n", cr->Coderep_id(), Usecnt(cr));
    }
  }
}

// ====================================================================
// Print_live_bits - for use in dbx only
// ====================================================================
void
BITWISE_DCE::Print_livebits(INT32 cr_id) 
{
  fprintf(TFile, "0x%" SCNx64 "\n", _livebits[cr_id]);
}

/* CVTL-RELATED finish */
