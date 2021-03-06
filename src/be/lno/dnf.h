/*

  Copyright (C) 2000, 2001 Silicon Graphics, Inc.  All Rights Reserved.

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


// This is really -*- C++ -*-

#ifndef dnf_INCLUDED
#define dnf_INCLUDED "dnf.h"

#include <sys/types.h>
#include <stdio.h>
#include <assert.h>

#include "defs.h"
#include "cxx_memory.h"
#include "mat.h"
#include "infin.h"
#include "lnoutils.h"
#include "soe.h"

enum CLAUSE_TYPE {CLAUSE_DISJ, CLAUSE_ATOM};

/* The nice thing about soe's is that they represent a conjunct. So,
   they can be the building blocks of our disjunctive general 
   clauses. A clause is either an soe (i.e. a atom-clause clause,
   or it can be the a disj of clauses. Note that nothing at this
   stage forces the conjunct of two conjuncts to be represented 
   as a single conjunct. That will be imposed by a normalization
   phase to be performed at the discretion of a user later */

class LINEAR_CLAUSE {
private:
  CLAUSE_TYPE  _t;
  MEM_POOL    *_m;
  union {
    SYSTEM_OF_EQUATIONS    *_atom;
    struct {
      INT32                 _nconj;
      SYSTEM_OF_EQUATIONS **_conj;
    } _disj;
  } _u;
  friend LINEAR_CLAUSE *
  _xcombine_atom_with_disj(LINEAR_CLAUSE *l1, LINEAR_CLAUSE *l2);
  friend LINEAR_CLAUSE *
  _xcombine_disj_with_disj(LINEAR_CLAUSE *l1, LINEAR_CLAUSE *l2);
  enum CLAUSE_TYPE CLAUSE_type() {
    return _t;
  }
  SYSTEM_OF_EQUATIONS *CLAUSE_atom() {
    assert (_t == CLAUSE_ATOM);
    return _u._atom;
  }
  INT32 CLAUSE_nconj () {
    assert (_t == CLAUSE_DISJ);
    return _u._disj._nconj;
  }
  SYSTEM_OF_EQUATIONS **CLAUSE_conj() {
    assert (_t == CLAUSE_DISJ);
    return _u._disj._conj;
  }
  SYSTEM_OF_EQUATIONS *CLAUSE_conj_ith(INT32 i) {
    return _u._disj._conj[i];
  }
  MEM_POOL *CLAUSE_mem_pool() {
    return _m;
  }
public:
  LINEAR_CLAUSE (SYSTEM_OF_EQUATIONS *soe, MEM_POOL *pool);
  LINEAR_CLAUSE (SYSTEM_OF_EQUATIONS **soe_list,
		 INT32 count, MEM_POOL *pool);
  friend LINEAR_CLAUSE *
  combine_clauses (LINEAR_CLAUSE *l1, LINEAR_CLAUSE *l2);
  BOOL Is_Consistent();
  void Print (FILE *fp) const;
};

#endif
