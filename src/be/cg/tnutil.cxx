/*
 * Copyright (C) 2008 PathScale, LLC.  All Rights Reserved. 
 */

/*
 * Copyright (C) 2006. QLogic Corporation. All Rights Reserved.
 */

/*
 * Copyright 2002, 2003, 2004, 2005, 2006 PathScale, Inc.  All Rights Reserved.
 */

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


/* ====================================================================
 * ====================================================================
 *
 * Module: tnutil.c
 * $Revision: 1.19 $
 * $Date: 05/05/12 12:41:10-07:00 $
 * $Author: tkong@hyalite.keyresearch $
 * $Source: be/cg/SCCS/s.tnutil.cxx $
 *
 * Description:
 *
 * Utility functions for support of the TN data structure.
 * Prototypes are in tn.h.
 *
 * ====================================================================
 * ====================================================================
 */

#define __STDC_LIMIT_MACROS
#include <stdint.h>
#ifdef USE_PCH
#include "cg_pch.h"
#endif // USE_PCH
#pragma hdrstop

#include "defs.h"
#include "config.h"
#include "erglob.h"
#include "xstats.h"
#include "tracing.h"

#include "strtab.h"
#include "tn.h"
#include "tn_list.h"
#include "ttype.h"

#include "const.h"
#include "targ_const.h"
#include "targ_sim.h"

#include "reg_live.h"
#include "gra_live.h"
#include "op_list.h"
#include "hb_hazards.h"
#include "register.h"
#include "targ_isa_registers.h"
#include "targ_proc_properties.h"
#include "targ_isa_enums.h"
#include "stblock.h"
#include "data_layout.h"	// for FP/SP

#ifdef TARG_ST
#include "config_targ_opt.h"	// for Enable_64_Bits_Ops
#include "cg_flags.h"  // for GRA_LIVE_Phase_Invoked
#include "gra_live.h"
//TB; for List_Software_Names
#include "config_list.h"
#include "lai_loader_api.h" // extension api
#include "cg_ssa.h"
#include "label_util.h"        // For Get_Label_BB
#endif

#ifdef TARG_ST
// Ensure > 0
#define DEFAULT_RCLASS_SIZE(rc)	\
	((REGISTER_bit_size(rc, REGISTER_CLASS_last_register(rc))+7)/8)
#else
#define DEFAULT_RCLASS_SIZE(rc)	\
	(REGISTER_bit_size(rc, REGISTER_CLASS_last_register(rc))/8)
#endif

/* ====================================================================
 *
 * Global data objects
 *
 * ====================================================================
 */

/* Various dedicated TNs: */
TN *RA_TN = NULL;
TN *SP_TN = NULL;
TN *FP_TN = NULL;
TN *Ep_TN = NULL;
TN *GP_TN = NULL;
TN *Zero_TN = NULL;
TN *Pfs_TN = NULL;
TN *True_TN = NULL;
TN *FZero_TN = NULL;
TN *FOne_TN = NULL;
TN *LC_TN = NULL;
#ifdef TARG_ST
TN *Link_TN;
TN *RS_TN;
TN *TP_TN;
TN *EH_Return_Stackadj_TN;
#endif

/* We currently always use the same dedicated TN for each
 * register-class/register pair. We save pointers to them here
 * so we can get at them later.
 */
#ifdef TARG_ST
static TN *ded_tns[ISA_REGISTER_CLASS_MAX_LIMIT + 1][REGISTER_MAX + 1];
#else
static TN *ded_tns[ISA_REGISTER_CLASS_MAX + 1][REGISTER_MAX + 1];
#endif
#ifdef TARG_ST200
static TN *paired_ded_tns[ISA_REGISTER_CLASS_MAX_LIMIT + 1][REGISTER_MAX + 1];
#endif
/* The register TNs are in a table named TNvec, indexed by their TN
 * numbers in the range 1..Last_TN.  The first part of the table, the
 * range 1..Last_Dedicated_TN, consists of TNs for various dedicated
 * purposes (e.g. stack pointer, zero, physical registers).  It is
 * followed by TNs for user variables and compiler temporaries, in the
 * range First_Regular_TN..Last_TN.
 */

/* Keep track of the TN_number for the last register TN generated. The 
 * first numbered TN is #1; #0 must remain unused (various algorithms
 * make special use of 0).
 */
TN_NUM Last_TN = 0;

/* TN_number of the last dedicated TN */
TN_NUM Last_Dedicated_TN = 0;
/* TN_number of the first non-dedicated TN. */
TN_NUM First_Regular_TN = 0;
/* TN_number of the first non-dedicated TN in the current REGION. */
TN_NUM First_REGION_TN = 0;

/* Mapping from TN numbers -> TNs for register TNs: */
TN **TN_Vec = NULL;		/* TN_number (TN_Vec[i]) == i */
#define TN_VEC_INIT	999
#define TN_VEC_INCR	499


/* Put constant TNs into a hash table to make searching faster. */

/* Set the hash table size to a power of 2 to make hashing fast. Dividing
 * by a prime number takes too long. It is OK to get a few extra duplicates.
 */
#define HASH_TABLE_SIZE  512	
#define HASH_VALUE(ivalue)	((INT)(ivalue) & (HASH_TABLE_SIZE-1))
#define	HASH_SYMBOL(st, offset) ( ((INT)(INTPS)((st)+(offset))) & (HASH_TABLE_SIZE-1))


static TN_LIST *Hash_Table[HASH_TABLE_SIZE];


/* ====================================================================
 *
 * Targ_TN_Add
 *
 * Some simple arithmetic operations that get done based upon the
 * sizes of TNs involved.  Generally used to manipulate the TN_value
 * and TN_offset of a TN.  Because the math may be done on one of these
 * values, the programmer passes in the appropriate one, and the size
 * passed is based upon TN_size of one/both of the involved TNs.
 * 
 * ====================================================================
 */
static INT64 
Targ_TN_Add( INT64 val1, INT16 size1, INT64 val2, INT16 size2 )
{
  if ( size1 <= sizeof(mINT32) && size2 <= sizeof(mINT32) )
    return ( ((mINT32)val1) + ((mINT32)val2) );
  else
    return ( val1 + val2 );
}



/* search for a previously built constant LIT_TN */
static TN *
Search_For_Previous_Constant (INT64 ivalue, INT size)
{
  TN_LIST *p;
  INT hash_value;
  TN *tn;

  hash_value = HASH_VALUE(ivalue);
  for(p = Hash_Table[hash_value]; p != NULL; p = TN_LIST_rest(p)) {
    tn = TN_LIST_first(p);
    if (TN_has_value(tn) && 
	TN_value(tn) == ivalue && 
	TN_size(tn) == size)
    {
      return tn;
    }
  }
  return NULL;
}


 /* search for a previously built symbol TN */
static TN *
Search_For_Previous_Symbol (ST *st, INT64 offset, INT relocs)
{
  TN_LIST *p;
  INT hash_value;
  TN *tn;

  hash_value = HASH_SYMBOL(st, offset);
  for (p = Hash_Table[hash_value]; p != NULL; p = TN_LIST_rest(p)) {
    tn = TN_LIST_first(p);
    if (TN_is_symbol(tn) && 
	TN_var(tn) == st && 
	TN_offset(tn) == offset && 
	TN_relocs(tn) == relocs)
    {
      return tn;
    }
  }
  return NULL;
}


/* ====================================================================
 *
 * Check_TN_Vec_Size
 *
 * Make sure TN_vec is big enough for another TN.
 * ====================================================================
 */
static void
Check_TN_Vec_Size ( void )
{
  static TN_NUM TN_Count = 0;	/* Size of mapping (not last index) */

  if ( TN_Count <= Last_TN+2 ) {
    if (TN_Vec == NULL) {
      TN_Count = TN_VEC_INIT;
      TN_Vec = (TN **) calloc ( TN_Count+1, sizeof(TN *) );
    }
    else {
      TN_Count += TN_VEC_INCR;
      TN_Vec = (TN **) realloc ( TN_Vec, (TN_Count+1)*sizeof(TN *) );
      memset ( &TN_Vec[TN_Count-TN_VEC_INCR+1], 0, (TN_VEC_INCR)*sizeof(TN *) );
    }
  }
}


/* ====================================================================
 *
 * Gen_TN
 *
 * Generate a new TN.  TN returned is completely zeroed.
 * ====================================================================
 */

static TN *
Gen_TN ( void )
{
  /* Allocate TNs for the duration of the PU. */
  TN *tn = TYPE_PU_ALLOC (TN);
  PU_TN_Cnt++;
  return tn;
}


/* ====================================================================
 *
 * Dup_TN
 *
 * Duplicate a TN with a new number.  
 *
 * The TN_GLOBAL_REG flag and any spill location associated with this TN 
 * is cleared in the new TN.
 *
 * ====================================================================
 */

TN *
Dup_TN ( TN *tn )
{
  TN *new_tn = Gen_TN();

  Is_True(! TN_is_dedicated(tn),("Dup_TN of a dedicated TN: TN%d",
          TN_number(tn)));

  *new_tn = *tn;
  if (!TN_is_constant(new_tn)) {
    Check_TN_Vec_Size ();
    Set_TN_number(new_tn,++Last_TN);
    Reset_TN_is_global_reg(new_tn);
    TN_Allocate_Register (new_tn, REGISTER_UNDEFINED);
    TNvec(Last_TN) = new_tn;
    /* copy over TN_home for rematerializable TNs. */
    if (!TN_is_rematerializable(tn) && !TN_is_gra_homeable(tn)) {
      Set_TN_spill(new_tn, NULL);
    }
  }

  return new_tn;
}

/* =======================================================================
 *
 *  Dup_TN_Even_If_Dedicated
 *
 *  It's not kosher to Dup a dedicated TN, but there are some legitimate
 *  reasons for wanting to do it if you know what you are doing.  For
 *  example, Transform_Conditional_Memory_OPs in (be/cg/la_ctran.c) has a
 *  legitimate reason for wanting to do this: it might be duping the stack
 *  pointer (for example) for use in a conditional move.  So here's a
 *  little wrapper for Dup_TN that will work even for a dedicated TN.
 *
 * ======================================================================= */
TN*
Dup_TN_Even_If_Dedicated(
  TN *tn
)
{
  TN tn_block;

  if ( ! TN_is_dedicated(tn) )
    return Dup_TN(tn);
  else {
    tn_block = *tn;

    Reset_TN_is_dedicated(&tn_block);
    TN_Allocate_Register (&tn_block, REGISTER_UNDEFINED);

    return Dup_TN(&tn_block);
  }
}


/* We currently always use the same dedicated TN for each
 * register-class/register pair. We save pointers to them here
 * so we can get at them later.
 */
static TN *f4_ded_tns[REGISTER_MAX + 1];
#ifdef KEY
static TN *v16_ded_tns[REGISTER_MAX + 1];
static TN *i1_ded_tns[REGISTER_MAX + 1];
static TN *i2_ded_tns[REGISTER_MAX + 1];
static TN *i4_ded_tns[REGISTER_MAX + 1];
#endif // KEY

/* ====================================================================
 *
 * Create_Dedicated_TN
 *
 * Create and initialize a new dedicated TN and remember it for later.
 *
 * ====================================================================
 */
static TN *
Create_Dedicated_TN (ISA_REGISTER_CLASS rclass, REGISTER reg)
{
#ifdef TARG_ST
  // Ensure size is always > 0 !
  INT size = DEFAULT_RCLASS_SIZE(rclass);
#else
  INT size = REGISTER_bit_size(rclass, reg) / 8;
#endif
#ifdef TARG_ST
  // Arthur: this is target dependent
  BOOL is_float = FALSE;
#else
  BOOL is_float = rclass == ISA_REGISTER_CLASS_float;
#endif

#ifdef TARG_X8664
  is_float |= ( rclass == ISA_REGISTER_CLASS_x87 );
#endif

  /* Allocate the dedicated TN at file level, because we reuse them 
   * for all PUs.
   */
  TN *tn = TYPE_SRC_ALLOC (TN);

  Check_TN_Vec_Size ();
  Set_TN_number(tn,++Last_TN);
  TNvec(Last_TN) = tn;
  Set_TN_is_dedicated(tn);
  Set_TN_register_class(tn, rclass);
  Set_TN_register(tn, reg);
  Set_TN_size(tn, size);
  if ( is_float ) Set_TN_is_float(tn);
  return(tn);
}

/* ====================================================================
 *
 * Init_Dedicated_TNs
 *
 * See interface description.
 *
 * ====================================================================
 */
void
Init_Dedicated_TNs (void)
{
  ISA_REGISTER_CLASS rclass;
  REGISTER reg;
  TN_NUM tnum = 0;

  FOR_ALL_ISA_REGISTER_CLASS(rclass) {
    for (reg = REGISTER_MIN; 
	 reg <= REGISTER_CLASS_last_register(rclass);
	 reg++
    ) {
      ++tnum;
      ded_tns[rclass][reg] = Create_Dedicated_TN(rclass, reg);
    }
  }

#ifdef TARG_ST
  // Arthur: if register has not been declared, make TN NULL:
  Zero_TN = CLASS_REG_PAIR_reg(CLASS_REG_PAIR_zero) == REGISTER_UNDEFINED ?
                 NULL : ded_tns[REGISTER_CLASS_zero][REGISTER_zero];
  Ep_TN = CLASS_REG_PAIR_reg(CLASS_REG_PAIR_ep) == REGISTER_UNDEFINED ?
                 NULL : ded_tns[REGISTER_CLASS_ep][REGISTER_ep];
  SP_TN = CLASS_REG_PAIR_reg(CLASS_REG_PAIR_sp) == REGISTER_UNDEFINED ?
                 NULL : ded_tns[REGISTER_CLASS_sp][REGISTER_sp];
  FP_TN = CLASS_REG_PAIR_reg(CLASS_REG_PAIR_fp) == REGISTER_UNDEFINED ?
                 NULL : ded_tns[REGISTER_CLASS_fp][REGISTER_fp];
  RA_TN = CLASS_REG_PAIR_reg(CLASS_REG_PAIR_ra) == REGISTER_UNDEFINED ?
                 NULL : ded_tns[REGISTER_CLASS_ra][REGISTER_ra];
  RS_TN = CLASS_REG_PAIR_reg(CLASS_REG_PAIR_rs) == REGISTER_UNDEFINED ?
                 NULL : ded_tns[REGISTER_CLASS_rs][REGISTER_rs];
  Pfs_TN = CLASS_REG_PAIR_reg(CLASS_REG_PAIR_pfs) == REGISTER_UNDEFINED ?
                 NULL : ded_tns[REGISTER_CLASS_pfs][REGISTER_pfs];
  True_TN = CLASS_REG_PAIR_reg(CLASS_REG_PAIR_true) == REGISTER_UNDEFINED ?
                 NULL : ded_tns[REGISTER_CLASS_true][REGISTER_true];
  FZero_TN = CLASS_REG_PAIR_reg(CLASS_REG_PAIR_fzero) == REGISTER_UNDEFINED ?
                 NULL : ded_tns[REGISTER_CLASS_fzero][REGISTER_fzero];
  FOne_TN = CLASS_REG_PAIR_reg(CLASS_REG_PAIR_fone) == REGISTER_UNDEFINED ?
                 NULL : ded_tns[REGISTER_CLASS_fone][REGISTER_fone];
  LC_TN = CLASS_REG_PAIR_reg(CLASS_REG_PAIR_lc) == REGISTER_UNDEFINED ?
                 NULL : ded_tns[REGISTER_CLASS_lc][REGISTER_lc];
  Link_TN = CLASS_REG_PAIR_reg(CLASS_REG_PAIR_link) == REGISTER_UNDEFINED ?
                 NULL : ded_tns[REGISTER_CLASS_link][REGISTER_link];
  // [SC] TLS support
  TP_TN = CLASS_REG_PAIR_reg(CLASS_REG_PAIR_tp) == REGISTER_UNDEFINED ?
                 NULL : ded_tns[REGISTER_CLASS_tp][REGISTER_tp];
  // [SC] Even in absolute code, the thread support may reference GP,
  // so always initialize GP_TN.
  /* SC: This must be distinct from the dedicated TN created
     for REGISTER_gp, because the TN_register field of this TN
     may be altered during compilation. */
  if (CLASS_REG_PAIR_reg(CLASS_REG_PAIR_gp) != REGISTER_UNDEFINED) {
    ++tnum; 
    GP_TN = Create_Dedicated_TN (REGISTER_CLASS_gp, REGISTER_gp);
  }
  else
    GP_TN = NULL;
    EH_Return_Stackadj_TN = NULL;

#ifdef TARG_ST200
  if (!True_TN) {
    // (cbr) we need a true_tn for predicated instructions that are sunk
    // into a psi instruction.
    ++tnum; 
    True_TN = Create_Dedicated_TN (ISA_REGISTER_CLASS_branch,
				   REGISTER_UNDEFINED); 
  }
#endif

#ifdef TARG_ARM
  if (!True_TN) {
    // (jv) we need a true_tn for predicated instructions that are sunk
    // into a psi instruction.
    ++tnum; 
    True_TN = Create_Dedicated_TN (ISA_REGISTER_CLASS_cpsr, 0); 
    Set_TN_register_and_class(True_TN, CLASS_AND_REG_true);
  }
#endif

#else

  /* Initialize the dedicated integer register TNs: */
  Zero_TN = ded_tns[REGISTER_CLASS_zero][REGISTER_zero];
  Ep_TN = ded_tns[REGISTER_CLASS_ep][REGISTER_ep];
  SP_TN = ded_tns[REGISTER_CLASS_sp][REGISTER_sp];
  FP_TN = ded_tns[REGISTER_CLASS_fp][REGISTER_fp];
  RA_TN = ded_tns[REGISTER_CLASS_ra][REGISTER_ra];
  Pfs_TN = ded_tns[REGISTER_CLASS_pfs][REGISTER_pfs];
  True_TN = ded_tns[REGISTER_CLASS_true][REGISTER_true];
  FZero_TN = ded_tns[REGISTER_CLASS_fzero][REGISTER_fzero];
  FOne_TN = ded_tns[REGISTER_CLASS_fone][REGISTER_fone];
  LC_TN = ded_tns[REGISTER_CLASS_lc][REGISTER_lc];
#endif
#if defined(KEY) && !defined(TARG_X8664)
  /* allocate gp tn.  this may use a caller saved register, so
   * we don't use the one allocated for $gp above.
   */
  GP_TN = Create_Dedicated_TN (REGISTER_CLASS_gp, REGISTER_gp);
  tnum++;
#endif

#ifndef TARG_ST
    for (reg = REGISTER_MIN; 
	 reg <= REGISTER_CLASS_last_register(ISA_REGISTER_CLASS_float);
	 reg++
    ) {
	++tnum;
        f4_ded_tns[reg] = Create_Dedicated_TN(ISA_REGISTER_CLASS_float, reg);
  	Set_TN_size(f4_ded_tns[reg], 4);
#ifdef KEY
	++tnum;
        v16_ded_tns[reg] = Create_Dedicated_TN(ISA_REGISTER_CLASS_float, reg);
  	Set_TN_size(v16_ded_tns[reg], 16);
#endif
    }
#ifdef KEY
    for (reg = REGISTER_MIN; 
	 reg <= REGISTER_CLASS_last_register(ISA_REGISTER_CLASS_integer);
	 reg++
    ) {
	++tnum;
        i1_ded_tns[reg] = Create_Dedicated_TN(ISA_REGISTER_CLASS_integer, reg);
  	Set_TN_size(i1_ded_tns[reg], 1);
	++tnum;
        i2_ded_tns[reg] = Create_Dedicated_TN(ISA_REGISTER_CLASS_integer, reg);
  	Set_TN_size(i2_ded_tns[reg], 2);
	++tnum;
        i4_ded_tns[reg] = Create_Dedicated_TN(ISA_REGISTER_CLASS_integer, reg);
  	Set_TN_size(i4_ded_tns[reg], 4);
    }
#endif // KEY
#endif // !TARG_ST
#ifdef TARG_ST200
  // [CG]: Have to initialize paired dedicated TNs used in prolog/epilog
  // generation. This code is target dependent but there is currently
  // no way to do otherwise.
  if (Enable_64_Bits_Ops) {
    ISA_REGISTER_SUBCLASS sc = ISA_REGISTER_SUBCLASS_paired;
    REGISTER_SET regset = REGISTER_SUBCLASS_members(sc);
    ISA_REGISTER_CLASS rclass = REGISTER_SUBCLASS_register_class(sc);
    for (REGISTER reg = REGISTER_SET_Choose(regset);
	 reg != REGISTER_UNDEFINED;
	 reg = REGISTER_SET_Choose_Next(regset, reg)) {
      ++tnum;
      paired_ded_tns[rclass][reg] = Create_Dedicated_TN(rclass, reg);
      Set_TN_size(paired_ded_tns[rclass][reg], DEFAULT_RCLASS_SIZE(rclass)*2);
    }
  }
#endif 
    Last_Dedicated_TN = tnum;
}


/* ====================================================================
 *
 * Build_Dedicated_TN
 *
 * See interface description.
 *
 * ====================================================================
 */
TN *
Build_Dedicated_TN (ISA_REGISTER_CLASS rclass, REGISTER reg, INT size)
{
#ifndef TARG_ST
#if defined( KEY)
    // check for F4 tns and 16-byte vector tns
  if (rclass == ISA_REGISTER_CLASS_float
	&& size != DEFAULT_RCLASS_SIZE(rclass) )
  {
        switch(size) {
	  case 4:  return f4_ded_tns[reg];
	  case 16: return v16_ded_tns[reg];
	}
  }
#else
  // check for F4 tns; someday may have to check for F10 tns too
  if (rclass == ISA_REGISTER_CLASS_float && size == 4
	&& size != DEFAULT_RCLASS_SIZE(rclass) )
  {
	return f4_ded_tns[reg];
  }
#endif
#endif //!TARG_ST
#ifdef KEY
  // check for I4 tns
  if (rclass == ISA_REGISTER_CLASS_integer
	&& size != DEFAULT_RCLASS_SIZE(rclass) )
  {
        switch(size) {
	  case 1: return i1_ded_tns[reg];
	  case 2: return i2_ded_tns[reg];
	  case 4: return i4_ded_tns[reg];
	}
  }
#endif // KEY
#ifdef TARG_ST
  // [CG] If size is the default size, use the dedicated tn
  // array
  if (size == 0 || size == DEFAULT_RCLASS_SIZE(rclass)) {
    return ded_tns[rclass][reg];
  }
  if(rclass > ISA_REGISTER_CLASS_STATIC_MAX) {
     ISA_REGISTER_SUBCLASS subclass;
     FOR_ALL_ISA_REGISTER_SUBCLASS(subclass) {
         const ISA_REGISTER_SUBCLASS_INFO * subclassInfo =
             ISA_REGISTER_SUBCLASS_Info(subclass);
         if(rclass == ISA_REGISTER_SUBCLASS_INFO_Class(subclassInfo) &&
            ((EXTENSION_get_REGISTER_SUBCLASS_bit_size(subclass)+CHAR_BIT - 1)
             / CHAR_BIT == size)) {
                 TN *res = Gen_Register_TN(rclass, size);
                 TN_Allocate_Register(res, reg);
                 Set_TN_is_dedicated(res);
                 return res;
             }
     }
  }
#ifdef TARG_ST200
  if (size == DEFAULT_RCLASS_SIZE(rclass)*2) {
    return paired_ded_tns[rclass][reg];
  }
#endif
  DevAssert(0, ("unexpected size, rclass:%d, reg:%d, size:%d", rclass, reg, size));
#else
  return ded_tns[rclass][reg];
#endif
}
 
TN *
Gen_Register_TN (ISA_REGISTER_CLASS rclass, INT size)
{
  Is_True(rclass != ISA_REGISTER_CLASS_UNDEFINED,
	  ("Gen_Register_TN called with undefined reg class"));

  if ( REGISTER_SET_EmptyP(REGISTER_CLASS_allocatable(rclass)) ) 
  {
	if(REGISTER_CLASS_register_count(rclass) != 1)
		printf("error\n");
	// only one reg in class, so make dedicated tn
  	FmtAssert(REGISTER_CLASS_register_count(rclass) == 1,
	      ("don't know how to make dedicated TN for class %s",
		REGISTER_CLASS_name(rclass)));
	return Build_Dedicated_TN(rclass, REGISTER_MIN, size);
  }
  else {
	TN *tn = Gen_TN();
  	Check_TN_Vec_Size ();
  	Set_TN_number(tn,++Last_TN);
  	TNvec(Last_TN) = tn;
#ifdef TARG_ST
    // [Reconfigurability] Removed initial useless limitation
    // NOTE: size is given in bytes. In reconfigurability context, we may have
    // registers upto 2048 bits, thus 256 bytes. Following assertion this is here
    // to check that size does not exceed sizeof(mUINT16)
    if ( size >= 65536) ErrMsg ( EC_TN_Size, size );
#else
  	if ( size > 32 ) ErrMsg ( EC_TN_Size, size );
#endif
  	Set_TN_size(tn, size);
#ifdef TARG_ST
    // Arthur: this is target dependent. 
    // TODO: parametrize this.
#else
  	if ( rclass == ISA_REGISTER_CLASS_float)  Set_TN_is_float(tn);
#ifdef TARG_X8664
  	if ( rclass == ISA_REGISTER_CLASS_x87)  Set_TN_is_float(tn);
#endif
#endif
    	Set_TN_register_class(tn, rclass);
  	return tn;
  }
}

#ifdef TARG_ST
/* ====================================================================
 *   Get_Normalized_TN_Value
 *
 *   [CG]: normalizes upper non significant bits of a TN.
 *   We normalize values by sign-extending or zero-extending
 *   from <size> to 8 bytes.
 *   For instance a TN of size 4 with 0x80000000 will have
 *   a 64 bits value of 0xffffffff80000000 if signed or 0x0000000080000000
 *   if not signed.
 *   The rational is to get always identical values if 2 values differ
 *   in the upper non significant bits.
 *   It is also done like this in the WHIRL.
 *   Note however that the input constant must already be correctly sign
 *   or zero extendend.
 * ====================================================================
 */
static INT64
Get_Normalized_TN_Value(INT64 ivalue, INT size, INT is_signed)
{
  FmtAssert(8*size <= 64, ("Get_Normalized_TN_Value: TN size is too large: %d\n", size));
  FmtAssert(8*size == 64 || (ivalue >= (- 1LL << (8*size-1)) &&
			     ivalue <= (((1LL << (8*size)) - 1LL))),
       ("Get_Normalized_TN_Value: %d-byte literal 0x%016llx is out-of-range", size, ivalue));

  return is_signed ? ((INT64)((ivalue) << (64 - size*8))) >> (64 - size*8):
    ((UINT64)((ivalue) << (64 - size*8))) >> (64 - size*8);
}

#endif

#if defined( KEY) && !defined(TARG_ST)
TN *
Gen_Typed_Register_TN (TYPE_ID mtype, INT size)
{
  ISA_REGISTER_CLASS rclass = Register_Class_For_Mtype (mtype);
  TN* tn;

  Is_True(rclass != ISA_REGISTER_CLASS_UNDEFINED,
	  ("Gen_Typed_Register_TN encountered undefined reg class"));

  /* If there is only one registers in a class, and it is not
     allocatable, then just return the dedicated TN representing that
     register. I'm not sure why this behavior is needed... */
  if ( REGISTER_SET_EmptyP(REGISTER_CLASS_allocatable(rclass)) &&
       (REGISTER_CLASS_register_count(rclass) == 1))
  {
    tn = Build_Dedicated_TN(rclass, REGISTER_MIN, size);
  }
  else {
	tn = Gen_TN();
  	Check_TN_Vec_Size ();
  	Set_TN_number(tn,++Last_TN);
  	TNvec(Last_TN) = tn;
  	//if ( size > 16 ) ErrMsg ( EC_TN_Size, size );
  	Set_TN_size(tn, size);

  	if ( rclass == ISA_REGISTER_CLASS_float
#ifdef TARG_X8664
	     || rclass == ISA_REGISTER_CLASS_x87
#endif
           )
	  Set_TN_is_float(tn);
    	Set_TN_register_class(tn, rclass);
  }

  return tn;
} 
#endif

// gen unique literal tn
TN *
Gen_Unique_Literal_TN (INT64 ivalue, INT size
#ifdef TARG_ST
                       , INT is_signed
#endif
                       )
{
	TN *tn = Gen_TN ();
#ifdef TARG_ST
  ivalue = Get_Normalized_TN_Value(ivalue, size, is_signed);
#endif
	Set_TN_size(tn, size);
	Set_TN_is_constant(tn);
    	Set_TN_has_value(tn);
	Set_TN_value(tn, ivalue);
  	return tn;
}

/* ====================================================================
 *
 * Gen_Literal_TN
 *
 * Produce a literal TN with the given literal value and size, either a
 * pre-existing one or a newly created one.
 *
 * ====================================================================
 */

TN *
Gen_Literal_TN ( INT64 ivalue, INT size
#ifdef TARG_ST
                 , INT is_signed 
#endif
                 )
{
  INT hash_value;
  TN *tn;
  
#ifdef TARG_ST
  ivalue = Get_Normalized_TN_Value(ivalue, size, is_signed);
#endif

  Is_True(size != 4 || (ivalue >= -2147483648LL && ivalue <= 4294967295LL),
	  ("Gen_Literal_TN: 4-byte literal 0x%016" SCNx64 " is out-of-range", ivalue));

  /* Check if there is already a constant TN with this value. Otherwise
   * create a new one and add it to the hash table. 
   */
  tn = Search_For_Previous_Constant (ivalue, size);
  if (tn == NULL) {
    tn = Gen_TN ();
    Set_TN_size(tn, size);
    Set_TN_is_constant(tn);
    Set_TN_has_value(tn);
#ifdef TARG_ST
    // [CG] : Why not using the write accessor?
    Set_TN_value(tn, ivalue);
#else
    TN_value(tn) = ivalue;
#endif

    hash_value = HASH_VALUE(ivalue);
    Hash_Table[hash_value] = 
		  TN_LIST_Push (tn, Hash_Table[hash_value], &MEM_pu_pool);
  }
  return tn;
}
 
TN *
Gen_Enum_TN (ISA_ENUM_CLASS_VALUE ecv)
{
	TN *tn = Gen_TN ();
	Set_TN_size(tn, 2);
	Set_TN_is_constant(tn);
	Set_TN_is_enum(tn);
	Set_TN_enum(tn, ecv);
	return tn;
}

/* ====================================================================
 *
 * Gen_Symbol_TN
 *
 * Produce a TN with the given symbol value, offset and relocs. 
 * This TN will represent the value of the symbol's address plus the 
 * offset.  Note that, for stack frame symbols, the address represented 
 * is relative to the stack pointer rather than absolute.
 *
 * ====================================================================
 */

TN *
Gen_Symbol_TN ( ST *st, INT64 offset, INT32 relocs)
{
  TN *tn;
  INT hash_value;

  /* First try to find an existing symbol TN */
  tn = Search_For_Previous_Symbol (st, offset, relocs);
  if (tn == NULL) {
    tn = Gen_TN ();
    Set_TN_size(tn, Pointer_Size);
    Set_TN_is_constant(tn);
    Set_TN_is_symbol(tn);
    Set_TN_var(tn, st);
    TN_offset(tn) = offset;
    TN_relocs(tn) = relocs;

    hash_value = HASH_SYMBOL(st, offset);
    Hash_Table[hash_value] = 
		  TN_LIST_Push (tn, Hash_Table[hash_value], &MEM_pu_pool);
  }
  return tn;
}
 

/* ====================================================================
 *
 * Gen_Label_TN
 *
 * Produce a TN with the given label value and offset.  This TN will
 * represent the value of the label's address plus the offset.
 *
 * ====================================================================
 */

TN *
Gen_Label_TN ( LABEL_IDX lab, INT64 offset )
{
  TN *tn;

  /* Make an new one and put it into the table: */
  tn = Gen_TN ();
  Set_TN_size(tn, Pointer_Size);
  Set_TN_is_constant(tn);
  Set_TN_is_label(tn);
  TN_label(tn) = lab;
  TN_offset(tn) = offset;
  return tn;
}

TN *
Gen_Tag_TN ( LABEL_IDX tag)
{
  TN *tn;

  /* Make an new one and put it into the table: */
  tn = Gen_TN ();
  Set_TN_size(tn, Pointer_Size);
  Set_TN_is_constant(tn);
  Set_TN_is_tag(tn);
  TN_label(tn) = tag;
  return tn;
}

/* ====================================================================
 *
 * Gen_Adjusted_TN
 *
 * Generate a TN which is identical to the given TN, but is 'adjust'
 * larger (or smaller if adjust is negative)
 *
 * ====================================================================
 */

TN *
Gen_Adjusted_TN ( TN *tn, INT64 adjust )
{
  TN *new_tn = NULL;

  FmtAssert (TN_is_constant(tn), ("Gen_Adjusted_TN: not a constant TN"));

  if (TN_has_value(tn)) {
    new_tn = Gen_Literal_TN ( 
	     Targ_TN_Add(TN_value(tn),TN_size(tn),adjust,TN_size(tn)), 
	     TN_size(tn));
  }
  else if ( TN_is_symbol(tn) ) {
    new_tn = Gen_Symbol_TN(TN_var(tn), TN_offset(tn)+adjust, TN_relocs(tn));
  }
  else if (TN_is_label(tn)) {
    new_tn = Gen_Label_TN (TN_label(tn), TN_offset(tn)+adjust);
  }
  else {
    ErrMsg( EC_Unimplemented,
	"Gen_Adjusted_TN: Cannot handle this type of constant" );
  }

  return new_tn;
}


/* ====================================================================
 *
 * sPrint_TN
 *
 * Format a TN to a string.  It uses the 'buf' passed in as the string.
 * Returns a pointer to buf.
 *
 * ====================================================================
 */

static char *
sPrint_TN (const TN *tn, BOOL verbose, char *buf )
{
  char *result = buf;

  if (tn == NULL) {
    buf += sprintf ( buf, "--nil--");
    return result;
  }

  if (TN_is_constant(tn)) {
    if ( TN_has_value(tn)) {
      buf += sprintf ( buf, "(0x%" SCNx64 ")", TN_value(tn) );
      if (TN_size(tn) == 4 && 
	  TN_value(tn) >> 32 != 0 &&
	  TN_value(tn) >> 31 != -1)
	buf += sprintf ( buf, "!!! TN_value=0x%" SCNx64 " is too big to fit in a word",
			 TN_value(tn));
    }
    else if (TN_is_enum(tn)) {
      buf += sprintf ( buf, "(enum:%s)", ISA_ECV_Name(TN_enum(tn)) );
    }
    else if ( TN_is_label(tn) ) {
      LABEL_IDX lab = TN_label(tn);
      const char *name = LABEL_name(lab);
      INT64 offset = TN_offset(tn);
      if ( offset == 0 ) {
	buf += sprintf ( buf, "(lab:%s)", name );
      }
      else {
	buf += sprintf ( buf, "(lab:%s+%" SCNd64 ")", name, offset );
      }
    } 
    else if ( TN_is_tag(tn) ) {
      LABEL_IDX lab = TN_label(tn);
      const char *name = LABEL_name(lab);
      buf += sprintf ( buf, "(tag:%s)", name );
    }
    else if ( TN_is_symbol(tn) ) {
      ST *var = TN_var(tn);
      buf += sprintf ( buf, "(sym" );
      switch (TN_relocs(tn)) {
      case TN_RELOC_NONE: break;
      case TN_RELOC_NEG: buf += sprintf ( buf, "-" ); break;
      case TN_RELOC_GPREL16: buf += sprintf (buf, "#gprel16"); break;
      case TN_RELOC_LOW16: buf += sprintf (buf, "#lo"); break;
      case TN_RELOC_HIGH16: buf += sprintf (buf, "#hi"); break;
      case TN_RELOC_HIGHER: buf += sprintf (buf, "#higher"); break;
      case TN_RELOC_HIGHEST: buf += sprintf (buf, "#highest"); break;
      case TN_RELOC_GOT_DISP: buf += sprintf (buf, "#got_disp"); break;
      case TN_RELOC_GOT_PAGE: buf += sprintf (buf, "#got_page"); break;
      case TN_RELOC_GOT_OFST: buf += sprintf (buf, "#got_ofst"); break;
      case TN_RELOC_CALL16: buf += sprintf (buf, "#call16"); break;
      case TN_RELOC_GOT_HI16: buf += sprintf (buf, "#got_hi16"); break;
      case TN_RELOC_GOT_LO16: buf += sprintf (buf, "#got_lo16"); break;
      case TN_RELOC_CALL_HI16: buf += sprintf (buf, "#call_hi16"); break;
      case TN_RELOC_CALL_LO16: buf += sprintf (buf, "#call_lo16"); break;
      case TN_RELOC_GPSUB: buf += sprintf (buf, "#gpsub"); break;
      case TN_RELOC_LO_GPSUB: buf += sprintf (buf, "#lo_gpsub"); break;
      case TN_RELOC_HI_GPSUB: buf += sprintf (buf, "#hi_gpsub"); break;
      case TN_RELOC_GPIDENT: buf += sprintf (buf, "#gpident"); break;
      case TN_RELOC_LO_GPIDENT: buf += sprintf (buf, "#lo_gpident"); break;
      case TN_RELOC_HI_GPIDENT: buf += sprintf (buf, "#hi_gpident"); break;
      case TN_RELOC_IA_GPREL22: buf += sprintf (buf, "#gprel22"); break;
      case TN_RELOC_IA_LTOFF22: buf += sprintf (buf, "#ltoff22"); break;
      case TN_RELOC_IA_LTOFF_FPTR: buf += sprintf (buf, "#ltoff_fptr"); break;
      }
      if (ST_class(var) == CLASS_CONST)
      	buf += sprintf ( buf, ":%s)", Targ_Print(NULL, ST_tcon_val(var)));
      else
      	buf += sprintf ( buf, ":%s%+" SCNd64 ")", ST_name(var), TN_offset(tn) );
    } 
    else {
      ErrMsg (EC_Unimplemented, "sPrint_TN: illegal constant TN");
    }
  }
  else {  /* register TN */
    if (TN_is_global_reg(tn)) {
      buf += sprintf ( buf, "GTN%d", TN_number(tn) );
    }
    else {
      buf += sprintf ( buf, "TN%d", TN_number(tn) );
    }
    if (TN_register(tn) != REGISTER_UNDEFINED) {
      if (TN_register(tn) <= REGISTER_CLASS_last_register(TN_register_class(tn))) {
	buf += sprintf (buf, "(%s)", 
		REGISTER_name(TN_register_class(tn), TN_register(tn)));
      } else {
	buf += sprintf (buf, "(%d,%d)", TN_register_class(tn), TN_register(tn));
      }
    }
    if (TN_is_save_reg(tn)) {
	buf += sprintf (buf, "(sv:%s)", 
		REGISTER_name(TN_save_rclass(tn), TN_save_reg(tn)));
    }
  }
  if (tn && Get_Trace(TP_CG, 8))
    buf += sprintf(buf, ":%d", TN_size(tn));
  
  if ( verbose ) {
    buf += sprintf ( buf, "[f:0x%x s:%d]", TN_flags(tn), TN_size(tn) );
  }
  return result;
}

/* ====================================================================
 *
 * fPrint_TN
 *
 * Print a TN to the given file.
 * Assume that 'fmt' has a %s in it for the TN string.
 *
 * ====================================================================
 */

void
fPrint_TN ( FILE *f, const char *fmt, const TN *tn)
{
  char buf[1024];
  char *s = sPrint_TN (tn, FALSE, buf);
  Is_True(strlen(s) < 1024, ("fPrint_TN buf overflowed"));
  fprintf(f, fmt, s);
}


/* ====================================================================
 *
 * Print_TN
 *
 * Print a TN to the trace file.
 *
 * ====================================================================
 */

void
Print_TN (const TN *tn, BOOL verbose, FILE *f) {
  char buf[1024];
  char *s = sPrint_TN (tn, verbose, buf);
  Is_True (strlen (s) < 1024, ("Print_TN buf overflowed"));
  fprintf (f, "%s", s);
}

void
Print_TN_List (FILE *f, TN_LIST *tnl) {
  INT count = 0;
  if (tnl != NULL) {
    fprintf(f, "\t");
    for (TN_LIST *tmp=tnl; tmp; tmp=TN_LIST_rest(tmp)) {
      fPrint_TN(f, "%s ", TN_LIST_first(tmp));
      if (++count == 5) {
	count = 0;
	fprintf(f, "\n\t");
      }
    }
    fprintf(f, "\n");
  }
}

/* dump_tn can be called from the debugger */
void
dump_tn (TN *tn)
{
  fPrint_TN (stdout, "%s\n", tn);
}

/* ====================================================================
 *
 * Print_TNs
 *
 * Print all TNs to the trace file.
 *
 * ====================================================================
 */

void
Print_TNs (FILE *f) {
  INT num_lits = 0;

  fprintf (f, "\n----------  TNs -------------\n");
  fprintf (f, "Last_Dedicated_TN = %d\n", Last_Dedicated_TN);
  fprintf (f, "First_Regular_TN  = %d\n", First_Regular_TN);
  fprintf (f, "Last_TN \t  = %d\n", Last_TN);
  for (INT i=1; i<=Last_TN; ++i) {
    if (TNvec (i) == NULL) continue;
    Print_TN (TNvec (i), TRUE, f);
    fprintf (f, "\n" );
  }

  fprintf (f, "\n---------- Literal  TNs -------------\n");
  for (INT i = 0; i < HASH_TABLE_SIZE; i++ ) {
    TN_LIST *p;
    for (p = Hash_Table[i]; p != NULL; p = TN_LIST_rest (p)) {
      Print_TN (TN_LIST_first (p), TRUE, f);
      fprintf (f, "\n");
      num_lits++;
    }
  }
  fprintf (f, "Number of Literal TNs  = %d\n", num_lits);
}

/* ====================================================================
 *
 * Init_TNs_For_PU
 *
 * This routine should be called before each PU to initialize the TNs
 * and the associated data structures.
 * ====================================================================
 */

void
Init_TNs_For_PU (void)
{
  TN *tn;
  TN_NUM tnnum;

  /* reset the fields of dedicated TNs */
  for ( tnnum = 0; tnnum <= Last_Dedicated_TN; tnnum++ ) {
    if ((tn = TNvec(tnnum)) != NULL) {
      Reset_TN_is_global_reg (tn);
      Set_TN_spill(tn, NULL);
    }
  }

  /* clear out the hash table */
  memset(Hash_Table, 0, sizeof(Hash_Table));

  /* reset Last_TN*/
  Last_TN = Last_Dedicated_TN;
  First_Regular_TN = Last_Dedicated_TN + 1;

  if( GP_TN != NULL ){
    /* reset GP_TN to point to $gp during code expansion, in case it was
     * changed by the last PU.  otherwise, Convert_WHIRL_To_OPs et. al.,
     * get confused.
     */
    Set_TN_register(GP_TN, REGISTER_gp);
  }
}

/* ====================================================================
 *
 * Init_TNs_For_REGION
 *
 * This routine should be called before each REGION to initialize the TNs.
 * Except for constants and dedicated TNs, the current REGION should
 * only reference TNs with numbers in the range
 * First_REGION_TN thru Last_TN.
 *
 * ====================================================================
 */

void
Init_TNs_For_REGION (void)
{
  TN *tn;
  TN_NUM tnnum;

  /* reset the fields of dedicated TNs */
  for ( tnnum = 0; tnnum <= Last_Dedicated_TN; tnnum++ ) {
    if ((tn = TNvec(tnnum)) != NULL) {
      /*
       * We do not clear the register_class since this may
       * be shared with an earlier REGION
       */
      Reset_TN_is_global_reg (tn);
      Set_TN_spill(tn, NULL);
    }
  }

  First_REGION_TN = Last_TN + 1;
}

/* =======================================================================
 *
 *  Find_TN_with_Matching_Register
 *
 *  See interface description.
 *
 * =======================================================================
 */
TN *
Find_TN_with_Matching_Register( TN *tn0, TN_LIST *list )
{
  TN_LIST *tnl;
  TN *tnx;
  REGISTER r0, rx;
  INT c0, cx;

  r0 = TN_register( tn0 );
  c0 = TN_register_class( tn0 );
  for ( tnl = list; tnl != NULL; tnl = TN_LIST_rest( tnl ) ) {
    tnx = TN_LIST_first( tnl );
    rx = TN_register( tnx );
    cx = TN_register_class( tnx );
    if (    ( r0 == rx )
	 && ( c0 == cx ) )
      return tnx;
  }
  return (TN *)NULL;
}

//TODO: probably want to move this generic routine elsewhere.
static inline BOOL
Is_OP_Cond(OP *op)
{
  // Conditional moves or predicated instructions have this property.
  if (OP_cond_def(op)) return TRUE;

  BB *bb = OP_bb(op);

  // OPs filled in the delay slot of branch-likely instrs. have the
  // same property as well.

  if (PROC_has_branch_delay_slot()) {
    if (Is_Delay_Slot_Op(op, bb) && OP_likely(BB_branch_op(bb)))
      return TRUE;
  }

  return FALSE;

}

/* ====================================================================
 *
 *  TN_Reaching_Value_At_Op
 *
 *  See interface description.
 *
 * ====================================================================
 */
OP *
TN_Reaching_Value_At_Op(
  TN *tn,
  OP *op,
  DEF_KIND *kind,
  BOOL reaching_def
)
{
  OP *value_op;  // value_op, could either be a defop or a useop.
  BB *bb;
  INT cnt;

#define MAX_BB_THRESHOLD    30     // Don't look beyond 30 predecessor blocks.
                                   // Results of finding very unlikely.
#ifdef TARG_ST
  if (reaching_def && SSA_Active()) {
    value_op = TN_ssa_def(tn);
    if (value_op == NULL) {
      *kind = VAL_UNKNOWN;
      return NULL;
    }
    if (Is_OP_Cond(value_op)) {
      if (OP_has_predicate(value_op) && OP_has_predicate(op)) {
	/* (cbr) predicate operand # is not necessary constant */
	int idx1 = OP_find_opnd_use(value_op, OU_predicate);
	int idx2 = OP_find_opnd_use(op, OU_predicate);

	TN *p1 = OP_opnd((OP*) value_op, idx1);
	TN *p2 = OP_opnd((OP*) op, idx2);
	// (cbr) Support for guards on false
	if (TNs_Are_Equivalent (p1, p2) &&
	    OP_Pred_False (value_op, idx1) == OP_Pred_False (op, idx2)) {
	  *kind =  VAL_COND_DEF;
	  return value_op;
	}
      }
      *kind = VAL_COND_DEF;
      return NULL;
    }
    // In case of a PSI operation, consider this is a conditional
    // relation. A more accurate result would require to make a
    // projection of the PSI operation on the predicate for op, and
    // see if there is only one reaching definition.
    if (OP_psi(value_op)) {
      *kind =  VAL_COND_DEF;
      return value_op;
    }
    *kind = VAL_KNOWN;
    return value_op;
  }
#endif


  if (TN_register(tn) != REGISTER_UNDEFINED) {
    REGISTER reg = TN_register(tn);
#ifdef TARG_ST
    INT nregs = TN_nhardregs(tn);
#endif
    ISA_REGISTER_CLASS rc = TN_register_class(tn);
    bb = OP_bb(op);
    value_op = (reaching_def) ? OP_prev(op) : OP_next(op);
    cnt = 0;
    do {
      while (value_op) {
	if (reaching_def) {
#ifdef TARG_ST
	  INT regs_matched = OP_Defs_Regs(value_op, rc, reg, nregs);
	  if (regs_matched > 0) {
	    if (regs_matched != nregs) {
	      // Do not return def of multi-reg TN unless all the regs
	      // are defined
	      return NULL;
	    } else if (Is_OP_Cond(value_op)) {
#else
	  if (OP_Defs_Reg(value_op, rc, reg)) {
	    if (Is_OP_Cond(value_op)) {
#endif
	      if (OP_has_predicate(value_op) && OP_has_predicate(op)) {
#ifdef TARG_ST
                /* (cbr) predicate operand # is not necessary constant */
                int idx1 = OP_find_opnd_use(value_op, OU_predicate);
                int idx2 = OP_find_opnd_use(op, OU_predicate);

		TN *p1 = OP_opnd((OP*) value_op, idx1);
		TN *p2 = OP_opnd((OP*) op, idx2);

#else
		TN *p1 = OP_opnd((OP*) value_op, OP_PREDICATE_OPND);
		TN *p2 = OP_opnd((OP*) op, OP_PREDICATE_OPND);
#endif
#ifdef TARG_ST
                // (cbr) Support for guards on false
                if (TNs_Are_Equivalent (p1, p2) &&
                    OP_Pred_False (value_op, idx1) == OP_Pred_False (op, idx2)) {
#else
		if (p1 == p2) {
#endif
		  *kind =  VAL_COND_DEF;
		  return value_op;
		}
	      }

	      *kind = VAL_COND_DEF;
	      return NULL;
	    } else {
	      *kind = VAL_KNOWN;
	      return value_op;
	    }
	  }
	} else {
#ifdef TARG_ST
	  INT regs_matched = OP_Refs_Regs(value_op, rc, reg, nregs);
	  if (regs_matched > 0) {
	    if (regs_matched != nregs) {
	      // Do not return ref of multi-reg TN unless all the regs
	      // are referenced.
	      return NULL;
	    } else if (Is_OP_Cond(value_op)) {
#else
	  if (OP_Refs_Reg(value_op, rc, reg)) {
	    if (Is_OP_Cond(value_op)) {
#endif
	      if (OP_has_predicate(value_op) && OP_has_predicate(op)) {
#ifdef TARG_ST
                /* (cbr) predicate operand # is not necessary constant */
                int idx1 = OP_find_opnd_use(value_op, OU_predicate);
                int idx2 = OP_find_opnd_use(op, OU_predicate);

		TN *p1 = OP_opnd((OP*) value_op, idx1);
		TN *p2 = OP_opnd((OP*) op, idx2);
#else
		TN *p1 = OP_opnd((OP*) value_op, OP_PREDICATE_OPND);
		TN *p2 = OP_opnd((OP*) op, OP_PREDICATE_OPND);
#endif
#ifdef TARG_ST
                // (cbr) Support for guards on false
                if (TNs_Are_Equivalent (p1, p2) &&
                    OP_Pred_False (value_op, idx1) == OP_Pred_False (op, idx2)) {
#else
		if (p1 == p2) {
#endif
		  *kind =  VAL_COND_USE;
		  return value_op;
		}
	      }

	      *kind = VAL_COND_USE;
	      return NULL;
	    } else {
	      *kind = VAL_KNOWN;
	      return value_op;
	    }
	  }
	}
	value_op = (reaching_def) ? OP_prev(value_op) : OP_next(value_op);
      }

      if (bb) {
	BBLIST *edge;
	INT val_cnt = 0;
	BB *cur_bb = NULL;
	BB *val_bb = NULL;
	
	if (reaching_def) {
	  FOR_ALL_BB_PREDS(bb, edge) {
	    cur_bb = BBLIST_item(edge);
#ifdef KEY
	    // Ignore cur_bb only if cur_bb doesn't redefine the register.
	    // Bug 6104.
	    if (cur_bb == bb) {
	      OP *op;
	      bool redefined = FALSE;
	      FOR_ALL_BB_OPs(cur_bb, op) {
	        if (OP_Defs_Reg(op, rc, reg)) {
		  redefined = TRUE;
		  break;
	        }
	      }
	      if (!redefined) continue;
	    }
#else
	    if (cur_bb == bb) continue;	// ignore self predecessor
#endif
#ifdef TARG_ST
            INT n_live_out = NREGS_Live_Outof_BB(rc, reg, nregs, cur_bb);
	    val_cnt += (n_live_out == nregs)
              ? 1
	      : ((n_live_out > 0)
		 ? 2  // Force break out
                 : 0);
	    val_bb = (n_live_out == nregs) ? cur_bb : val_bb;
#else
	    BOOL live_out = REG_LIVE_Outof_BB(rc, reg, cur_bb);
	    val_cnt += (live_out) ? 1 : 0;
	    val_bb = (live_out) ? cur_bb : val_bb;
#endif
	  }
	} else {
	  FOR_ALL_BB_SUCCS(bb, edge) {
	    cur_bb = BBLIST_item(edge);
	    if (cur_bb == bb) continue;	// ignore self successor
#ifdef TARG_ST
            INT n_live_in = NREGS_Live_Into_BB(rc, reg, nregs, cur_bb);
	    val_cnt += (n_live_in == nregs)
              ? 1
              : ((n_live_in > 0)
		 ? 2 // Force break out
                 : 0);
	    val_bb = (n_live_in == nregs) ? cur_bb : val_bb;
#else
	    BOOL live_in = REG_LIVE_Into_BB(rc, reg, cur_bb);
	    val_cnt += (live_in) ? 1 : 0;
	    val_bb = (live_in) ? cur_bb : val_bb;
#endif
	  }
	}
	bb = (val_cnt > 1) ? NULL : val_bb;

	if (bb == NULL || BB_call(bb)) break;

	value_op = (reaching_def) ? BB_last_op(bb) : BB_first_op(bb);
      }
    } while (++cnt < MAX_BB_THRESHOLD); // circuit-breaker

    *kind = VAL_UNKNOWN;
    return NULL;
  }

  /* See if there is a definition preceding the <op> or a use succeeding it.
   */
  bb = OP_bb(op);
  value_op = (reaching_def) ? OP_prev(op) : OP_next(op);
  cnt = 0;
  do {
    while (value_op) {
      if (reaching_def) {
	if (OP_Defs_TN(value_op, tn)) {
	  if (Is_OP_Cond(value_op)) {
	    if (OP_has_predicate(value_op) && OP_has_predicate(op)) {
#ifdef TARG_ST
                /* (cbr) predicate operand # is not necessary constant */
                int idx1 = OP_find_opnd_use(value_op, OU_predicate);
                int idx2 = OP_find_opnd_use(op, OU_predicate);

		TN *p1 = OP_opnd((OP*) value_op, idx1);
		TN *p2 = OP_opnd((OP*) op, idx2);
#else
	      TN *p1 = OP_opnd((OP*) value_op, OP_PREDICATE_OPND);
	      TN *p2 = OP_opnd((OP*) op, OP_PREDICATE_OPND);
#endif	   
#ifdef TARG_ST
                // (cbr) Support for guards on false
                if (TNs_Are_Equivalent (p1, p2) &&
                    OP_Pred_False (value_op, idx1) == OP_Pred_False (op, idx2)) {
#else   
	      if (p1 == p2) {
#endif
		*kind =  VAL_COND_DEF;
		return value_op;
	      }
	    }

	    *kind = VAL_COND_DEF;
	    return NULL;
	  } else {
	    *kind = VAL_KNOWN;
	    return value_op;
	  }
	}
      } else {
	if (OP_Refs_TN(value_op, tn)) {
	  if (Is_OP_Cond(value_op)) {
	    if (OP_has_predicate(value_op) && OP_has_predicate(op)) {
#ifdef TARG_ST
                /* (cbr) predicate operand # is not necessary constant */
                int idx1 = OP_find_opnd_use(value_op, OU_predicate);
                int idx2 = OP_find_opnd_use(op, OU_predicate);
		TN *p1 = OP_opnd((OP*) value_op, idx1);
		TN *p2 = OP_opnd((OP*) op, idx2);
#else
	      TN *p1 = OP_opnd((OP*) value_op, OP_PREDICATE_OPND);
	      TN *p2 = OP_opnd((OP*) op, OP_PREDICATE_OPND);
#endif	      
#ifdef TARG_ST
              // (cbr) Support for guards on false
                if (TNs_Are_Equivalent (p1, p2) &&
                    OP_Pred_False (value_op, idx1) == OP_Pred_False (op, idx2)) {
#else
	      if (p1 == p2) {
#endif
		*kind =  VAL_COND_USE;
		return value_op;
	      }
	    }

	    *kind = VAL_COND_USE;
	    return NULL;
	  } else {
	    *kind = VAL_KNOWN;
	    return value_op;
	  }
	}
      }
      value_op = (reaching_def) ? OP_prev(value_op) : OP_next(value_op);
    }

    if (bb) {
      BB *new_bb = NULL;
      if (GRA_LIVE_Phase_Invoked) {
	BBLIST *edge;
	INT val_cnt = 0;
	BB *val_bb = NULL;
	BB *cur_bb = NULL;
	
	if (reaching_def) {
	  FOR_ALL_BB_PREDS(bb, edge) {
	    cur_bb = BBLIST_item(edge);
#ifdef KEY
	    // Ignore cur_bb only if cur_bb doesn't redefine the TN.
	    // Bug 6104.
	    if (cur_bb == bb) {
	      OP *op;
	      bool redefined = FALSE;
	      FOR_ALL_BB_OPs(cur_bb, op) {
	        if (OP_Defs_TN(op, tn)) {
		  redefined = TRUE;
		  break;
	        }
	      }
	      if (!redefined) continue;
	    }
#else
	    if (cur_bb == bb) continue;	// ignore self predecessor
#endif
#ifdef TARG_ST
	    if (!BB_bbregs(cur_bb)) continue;
#endif
	    BOOL live_out = GRA_LIVE_TN_Live_Outof_BB(tn, cur_bb);
	    val_cnt += (live_out) ? 1 : 0;
	    val_bb = (live_out) ? cur_bb : val_bb;
	  }
	} else {
	  FOR_ALL_BB_SUCCS(bb, edge) {
	    cur_bb = BBLIST_item(edge);
	    if (cur_bb == bb) continue;	// ignore self successor
#ifdef TARG_ST
	    if (!BB_bbregs(cur_bb)) continue;
#endif
	    BOOL live_in = GRA_LIVE_TN_Live_Into_BB(tn, cur_bb);
	    val_cnt += (live_in) ? 1 : 0;
	    val_bb = (live_in) ? cur_bb : val_bb;
	  }
	}
	new_bb = (val_cnt > 1) ? NULL : val_bb;
      } 
      // in case no gra_live or it is out of date (e.g. during hbf)
      if (new_bb == NULL) {
	if (reaching_def)
		new_bb = BB_Unique_Predecessor(bb);
	else
		new_bb = BB_Unique_Successor(bb);
      }
      bb = new_bb;
    }
    if (bb == NULL) break;

    value_op = (reaching_def) ? BB_last_op(bb) : BB_first_op(bb);
  } while (++cnt < MAX_BB_THRESHOLD); // circuit-breaker

  *kind = VAL_UNKNOWN;
  return NULL;
}


/* ====================================================================
 *
 * Rematerializable_IntConst
 *
 * If <tn> is rematerializable, and the result is an integer,
 * return the integer value through the out parameter <val>
 * and return TRUE; otherwise just return FALSE.
 *
 * ====================================================================
 */
static BOOL
Rematerializable_IntConst(
  TN *tn,
  INT64 *val
)
{
  OPCODE opcode;
  OPERATOR opr;
  WN *home = TN_home(tn);

  if (!TN_is_rematerializable(tn)) return FALSE;

  if (!home) {
    DevWarn("No home for rematerializable TN%d", TN_number(tn));
    return FALSE;
  }

  opcode = WN_opcode(home);
  opr = OPCODE_operator(opcode);

  if (opr != OPR_INTCONST) return FALSE;

  switch (opcode) {
  case OPC_I8INTCONST:
  case OPC_U8INTCONST:
#ifdef TARG_X8664 
  // Bug 3262 - zero-extend; to be complete, we should zero-extend 
  // OPC_I4INTCONST also. We will be conservative, since this case
  // might have been handled already in the back-end.
  case OPC_U4INTCONST:
#endif
    *val = WN_const_val(home);
    break;
  case OPC_I4INTCONST:
#ifndef TARG_X8664 // see above
  case OPC_U4INTCONST:
#endif

    /* Even for U4 we sign-extend the value
     * so it matches what we want register to look like
     */
    *val = (INT32)WN_const_val(home);
    break;
  default:
    return FALSE;
  }

  return TRUE;
}


/* ====================================================================
 *
 *  TN_Value_At_Op
 *
 *  See interface description.
 *
 * ====================================================================
 */
BOOL
TN_Value_At_Op(
  TN *tn,
  OP *use_op,
  INT64 *val
)
{
  INT iters = 5;

  do {
    OP *def_op;

    DEF_KIND kind;
    if (TN_is_constant(tn)) {
      if (!TN_has_value(tn)) break;
      *val = TN_value(tn);
      return TRUE;
    } else if (TN_is_zero_reg(tn)) {
      *val = 0;
      return TRUE;
    } else if (TN_is_rematerializable(tn)) {
      return Rematerializable_IntConst(tn, val);
    } else if (use_op && (def_op = TN_Reaching_Value_At_Op(tn, use_op, &kind, TRUE)) && (kind == VAL_KNOWN)) {
#ifdef TARG_ST
      if ((OP_iadd(def_op) || OP_ior(def_op))
#else
      if (   (OP_iadd(def_op) || OP_ior(def_op))
#endif
	  && TN_is_zero_reg(OP_opnd(def_op,0))
	  && TN_has_value(OP_opnd(def_op,1))
      ) {
	tn = OP_opnd(def_op, 1);
	use_op = def_op;
	continue;
#ifdef TARG_ST
      } else if ((SSA_Active() && OP_Is_Copy(def_op)) ||
		 (!SSA_Active() && OP_copy(def_op))) {
	tn = OP_opnd(def_op, OP_Copy_Operand(def_op));
#else
      } else if (OP_copy(def_op)) {
	tn = OP_opnd(def_op, OP_COPY_OPND);
#endif
	use_op = def_op;
	continue;
      }
    }
    return FALSE;
  } while (--iters);

  Lmt_DevWarn(1,("TN_Value_At_Op exceeded max iterations to find reaching def"));

  return FALSE;
}

#ifdef TARG_ST
static INT
bits (INT64 value)
{
  INT msb = 0;
  
  if (value <= 0) {
    msb = 1;
  } 
  if (value < 0) {
    value = ~value;
  }

  while (value) {
    value >>= 1;
    msb++;
  };
  return msb;
}

/* ====================================================================
 *
 *  TN_bitwidth
 *
 *  See interface description.
 *
 * ====================================================================
 */
INT
TN_bitwidth (const TN *tn)
{
  if (TN_is_register (tn)) {
    REGISTER reg = TN_register (tn);
    ISA_REGISTER_CLASS rclass = TN_register_class (tn);
    if (reg == REGISTER_UNDEFINED) {
      reg = REGISTER_CLASS_last_register (rclass);
    }
    return REGISTER_bit_size (rclass, reg) * TN_nhardregs (tn);
  } else if (TN_has_value (tn)) {
    return bits (TN_value (tn));
  } else
    return 8 * TN_size (tn);
}
#endif

/* following routines were moved here from symconst_util */

/* These should be values which won't fit in any 32-bit range.
 * The +/- 1 adjustments are to make sure that they don't match literal
 * classes that look for something with only the upper byte non-zero.
 * However, for SVR3 compilations, INT64_Mxx is really INT32_Mxx, and
 * it shouldn't matter much as a temporary situation.
 */
#define	HUGE_MIN	(INT64_MIN/128+1)
#define HUGE_MAX	(INT64_MAX/128-1)

/* ====================================================================
 *
 * Get_TN_Range
 *
 * Get the current range of values possibly represented by a TN.  The
 * value is fixed for a numeric constant TN.  For a symbol TN, it is
 * the current value range.  For stack offset symbols, the range is 
 * its current offset +/- a tolerance.
 *
 * The return value indicates whether the range returned is usable for
 * combinations.  In some cases, we have TNs for which no reasonable
 * estimate is possible, but which only appear as operands where they
 * are known to be valid, i.e. labels in jumps.  In such cases, we
 * return a range of 1..1, which will fit in any literal class of
 * interest, but we return FALSE so that a caller with more complex
 * requirements doesn't go further with that range.
 *
 * WARNING:  The range calculated is not conservative in the sense that
 * the minimum and maximum values are true bounds on the value.
 * See Evaluate_Operand_Range for a more complete description of the
 * significance of this warning.
 *
 * ====================================================================
 */

static BOOL
Get_TN_Range (
  TN *tn,		/* TN to evaluate */
  INT64 *minval,	/* Result: Minimum value in range */
  INT64 *maxval )	/* Result: Maximum value in range */
{
  ST *st;
  ST *base_st;
#ifdef TARG_ST
  INT64 ofst;
#else
  INT64 ofst, base_ofst;
#endif

  /* For non-constant TNs, return a value range which won't fit
   * anywhere:
   */
  if ( ! TN_is_constant(tn) ) {
    *minval = HUGE_MIN;
    *maxval = HUGE_MAX;
    return FALSE;
  }

  /* Take care of the "simple" constant cases: */
  if ( TN_has_value(tn) ) {
    /* It has a value -- use it: */
    *minval = *maxval = TN_value(tn);
    return TRUE;
  } else if ( TN_is_label(tn) || TN_is_tag(tn)) {
    /* Return a dummy range of 1..1: */
    *minval = *maxval = 1;
    return FALSE;
  } else if ( ! TN_is_symbol(tn) ) {
    /* Return a value range which won't fit anywhere: */
    *minval = HUGE_MIN;
    *maxval = HUGE_MAX;
    return FALSE;
  } else if (TN_relocs(tn) != 0) {
    /* If the TN_relocs is non-zero, all the possible values are for 
     * 16bit relocations. So, assume it fits in 16 bits.
     */
    *minval = INT16_MIN;
    *maxval = INT16_MAX;
    return TRUE;
  }

  /* Now we have a symbol TN: */
  st = TN_var(tn);
  ofst = TN_offset(tn);
#ifdef TARG_ST
  base_st = Base_Symbol (st);
  if ((base_st == SP_Sym || base_st == FP_Sym)
      && Base_Offset_Is_Known (st)) {
    *minval = *maxval = Base_Offset (st) + ofst;
    return TRUE;
  }
#else
  Base_Symbol_And_Offset (st, &base_st, &base_ofst);

  if ( ST_on_stack(st)) {
    *minval = *maxval = base_ofst + ofst;
    return TRUE;
  } 
#endif
  /* shouldn't get this far */
  /* Return a value range which won't fit anywhere: */
  *minval = HUGE_MIN;
  *maxval = HUGE_MAX;
  return FALSE;
}

/* ====================================================================
 *
 * Evaluate_Operand_Range
 *
 * We are interested in the possible range of the given expression
 * involving a constant TN (which may be a symbol TN).
 *
 * The expression evaluated is:
 *	%val(tn1) +/- %val(tn2) + disp
 * where:
 *	%val(tnX) is the current value represented by tnX, as described
 *		for Get_TN_Range above.
 *
 *	+/- %val(tn2): whether $val(tn2) is added or subtracted is
 *		determined by 'expr_op.'  (It is ignored if tn2==NULL.)
 *
 *	disp is an arbitrary signed integer to add.
 *
 * If we are unable to produce a reasonable range (of the sort
 * necessary for checking validity as an immediate operand), we return
 * FALSE.  Otherwise, minval and maxval are set to the range bounds.
 *
 * WARNING:  The range calculated is not conservative in the sense that
 * the minimum and maximum values are true bounds on the value.
 * Rather, they reflect bounds which are reasonable for purposes of
 * immediate operand checking.  For instance, external symbol values
 * are returned as values in a 28-bit range for MIPS, because that's
 * the range within which we'll attempt direct calls.  They aren't at
 * the bounds of that range so that we can add "reasonable" offsets to
 * them and still get a positive answer to the query about fitting in
 * the immediate field.
 *
 * ====================================================================
 */

static BOOL
Evaluate_Operand_Range (
  TN	*tn1,		/* The primary TN (constant) */
  INT32	disp,		/* Displacement from symbolic value */
  INT64 *minval,	/* Result: Minimum value in range */
  INT64 *maxval )	/* Result: Maximum value in range */
{
  INT64 min1, max1;
  BOOL combine;

  if (tn1 == NULL) {
	*minval = *maxval = disp;
	return TRUE;
  }

  /* Get the TN values: */
  combine = Get_TN_Range ( tn1, &min1, &max1 );

  /* Adjust the first set of bounds: */
  if ( disp != 0 ) {
    if ( ! combine ) return FALSE;
    min1 += disp;
    max1 += disp;
  }

  /* Return our results: */
  *minval = min1;
  *maxval = max1;
  return TRUE;
}

/* ====================================================================
 *
 * Potential_Immediate_TN_Expr
 *
 * We are interested in whether a given expression involving a constant
 * TN (which may be a symbol TN) is a potential immediate operand for
 * the given operation.
 *
 * See Evaluate_Operand_Range for a description of the other operands'
 * treatment in answering the range question.
 *
 * ====================================================================
 */

BOOL
Potential_Immediate_TN_Expr (
  TOP opcode,		/* The operation of interest */
  TN	*tn1,		/* The primary TN (constant) */
  INT32	disp)		/* Displacement from symbolic value */
{
  INT64 lbound, hbound;

  /* Get the bounds and check them as operands: */
  return Evaluate_Operand_Range ( tn1, disp, &lbound, &hbound )
	   && TOP_Can_Have_Immediate ( lbound, opcode )
	   && TOP_Can_Have_Immediate ( hbound, opcode );
}


/* ====================================================================
 * ====================================================================
 *             TN Pair management for EMULATE LONGLONG
 * ====================================================================
 * ====================================================================
 */



/* ====================================================================
 *   Init_TN_Pair
 * ====================================================================
 */
void
Init_TN_Pair ()
{
  DevWarn("Init TN Pairs not implemented");
  return;
}

/* ====================================================================
 *   Add_TN_Pair
 *
 *   Adds a new TN_Pair to the table of TN pairs.
 * ====================================================================
 */
void
Add_TN_Pair (
  TN *tn1, 
  TN *tn2
)
{
  // Don't forget dedicated TN pairs ... see whirl2ops.cxx ...
  DevWarn("Add TN_Pair Not Implemented");
  return;
}

/* ====================================================================
 *   If_Get_TN_Pair
 * ====================================================================
 */
TN *
If_Get_TN_Pair (
  TN *tn
)
{
  FmtAssert(FALSE, ("If Get TN Pair Not Implemented"));
  return NULL;
}

/* ====================================================================
 *   Gen_Literal_TN_Pair
 *
 *   Make a TN_Pair holding a LONGLONG value.
 * ====================================================================
 */
TN *
Gen_Literal_TN_Pair (
  UINT64 val
)
{
  FmtAssert(FALSE, ("Get_Literal_TN_Pair Not Implemented"));
  return NULL;
}


#ifdef TARG_ST
//TB: Return the name of a register, given a tn and a subclass Useful
//for registers whose name depends on the register subclass. For
//instance on the VX extension register 6 is V6 or D3 depending on the
//subclass
const char *REGISTER_extended_name(TN* tn,
				   ISA_REGISTER_SUBCLASS sc) 
{
  const char *rname;
  ISA_REGISTER_CLASS rc = TN_register_class(tn);
  REGISTER reg = TN_register(tn);

  // If register is physical,print its real name, otherwise
  // virtual:
  if (reg != REGISTER_UNDEFINED) {
    if (REGISTER_SET_MemberP(REGISTER_SUBCLASS_members(sc), reg)
	&& REGISTER_SUBCLASS_reg_name(sc, reg)) {
      rname = REGISTER_SUBCLASS_reg_name(sc, reg);
    } 
    else if (List_Software_Names) {
      rname = ABI_PROPERTY_Reg_Name(rc, REGISTER_machine_id(rc, reg));
    } 
    else {
      rname = REGISTER_name(rc, reg);
    }
  }
  else {
    char *vname = TYPE_MEM_POOL_ALLOC_N(char, Malloc_Mem_Pool, 10);
    sprintf(vname, "%s%d", ISA_REGISTER_CLASS_Symbol(rc), TN_number(tn));
    rname = vname;
  }
  return rname;
}


/** 
 * Check TN equivalence
 * 
 * @param tn1 
 * @param tn2 
 * 
 * @return true if tn1 and tn2 are equivalent, false otherwise
 */
BOOL
TN_equiv(TN *tn1, TN *tn2) {

  if (tn1 == tn2)

    return TRUE;

  if (TN_is_register(tn1) &&
      TN_is_register(tn2) &&
      TNs_Are_Equivalent(tn1, tn2))
    return TRUE;

  if (TN_is_zero(tn1) && TN_is_zero(tn2))
    return TRUE;

  if (TN_has_value(tn1) && TN_has_value(tn2) &&
      TN_value(tn1) == TN_value(tn2))
    return TRUE;


  if (TN_is_symbol(tn1) && TN_is_symbol(tn2) &&
      TN_var(tn1) == TN_var(tn2) &&
      TN_offset(tn1) == TN_offset(tn2) &&
      TN_relocs(tn1) == TN_relocs(tn2))
    return TRUE;

  if (TN_is_label(tn1) && TN_is_label(tn2) &&
      Get_Label_BB(TN_label(tn1)) == Get_Label_BB(TN_label(tn2)) &&
      TN_offset(tn1) == TN_offset(tn2)) 
    return TRUE;

  if (TN_is_enum(tn1) && TN_is_enum(tn2) &&
      TN_enum(tn1) == TN_enum(tn2))
    return TRUE;

  return FALSE;
}

#endif
