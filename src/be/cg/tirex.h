#ifndef _INCLUDED_tirex_h
#define _INCLUDED_tirex_h

//TODO: put back into tirex.cxx when we got rid of cg_minir
#include <queue>
#include <stack>
#include <list>
typedef struct bbsstate {
  int preidx;      // pre-order of BBs for our Deapth First Search (DFS)
  int postidx;     // post-order
  bool isancestor; // tells if during the DFS this BB is an ancestor of the current BB
  bool traversed;  // tells if this BB has already been traversed (so skip it)
  bool isloopheader; // flag to specify if this BB is a loop header (can be self loop)
  unsigned loopidx;  // if loopheader, unique (dense) index. 0 for undefined
  bool innermost;   // if a loopheader, flag to specify if innermost loop  
  int loopdepth;    // the loop depth of the BB (0 if not in a BB) 
  bool irreducible;  // flag to specify if the corresponding loop has multiple entries
  std::stack<BB_NUM> BE; // list of source of back-edges of target BB
  std::stack<BB_NUM> P;  // list of non-back-edge predecessors of BB
  std::list<BB *> region; // BBs of the scheduling region (BB with identical loopdepth 
                          // within a common loop, or not within any loop)
  BB_NUM LP_parent;  // For union-find purpose. The root being the header of the largest
                     // discovered Strongly Connected Component (SCC)
  BB *loophead_bb;  // the parent in the loop nesting forest
  BB *entry_bb;     // first PU entry point from which this bb is accessible
  std::list<BB_NUM> loopchildren; // list of children in topological order of the DAG
} BBSSTATE;


extern void
tirex_init(FILE *file);

extern void
tirex_fini(void);

extern void
tirex_emit_pu(int stage);

#endif//_INCLUDED_tirex_h

