/*

  Copyright (C) 2000 Silicon Graphics, Inc.  All Rights Reserved.

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

  Contact information:  Silicon Graphics, Inc., 1600 Amphitheatre Pky,
  Mountain View, CA 94043, or:

  http://www.sgi.com

  For further information regarding this notice, see:

  http://oss.sgi.com/projects/GenInfo/NoticeExplan

*/

/* ====================================================================
 * Description:
 *  
 *  Declaration for exported cg interfaces.
 *
 *  void CG_Configure_Opt_Level( INT opt_level )
 *
 *      Call this to set/change the CG optimization level.  This is the only
 *      valid way to do this.  Directly setting CG_opt_level probably won't do
 *      what you want.
 *
 *
 * ====================================================================
 * ====================================================================
 */

#ifndef	lai_INCLUDED
#define	lai_INCLUDED

#include "opt_alias_interface.h"
#include "region_util.h"

#include "wn.h"
#include "dwarf_DST_mem.h"
#include "symtab.h"
#include "tn_map.h"

#include "cg_flags.h"

extern TN_MAP TN_To_PREG_Map;

/* type stubs - can't include appropriate files since
 * this file is included by be/com/driver.c ...
 */
struct bb;

extern BOOL PU_Has_Calls;
extern BOOL PU_References_GP;

extern BOOL CG_PU_Has_Feedback;

/* WOPT alias manager */
extern struct ALIAS_MANAGER *Alias_Manager;

#ifdef __cplusplus
extern "C" {
#endif

/* Generate code for the given REGION or PU
   The results are returned in a WHIRL statement-list
   attached to a BLOCK. */
extern WN *LAI_Emit_Code (
  WN            *rwn,           /* The REGION to compile */
  struct ALIAS_MANAGER *am,	/* WOPT alias manager */
  DST_IDX	pu_dst,		/* dst_idx for pu, (NULL for region) */
  BOOL		region		/* processing PU or region */
);

extern void LAI_PU_Initialize (WN *wn);
extern void LAI_PU_Finalize (void);


/* Process command line once for cg-specific options */
extern void LAI_Process_Command_Line (INT, char **, INT, char **);
extern void LAI_Configure_Opt_Level (INT opt_level);
extern void LAI_Init (void);	/* init once per compilation */
extern void LAI_Fini (void);	/* finalize once per compilation */

/* initialization for statics to keep the ST for locals generated
   when creating quad glue code for regions */
extern void Init_gen_quad_preg(void);

#ifdef __cplusplus
}
#endif

/* Print the IR for a program unit after a phase, if enabled: */
extern void Trace_IR (
  INT phase,		/* Phase after which to print */
  const char *pname,	/* Print name of phase */
  struct bb *bb		/* BB to print, or NULL */
);

/* Print IR, ST, TNs for a program unit after a phase, if enabled: */
extern void Check_for_Dump (
  INT phase,	/* Phase after which to print */
  struct bb *bb	/* BB to print, or NULL */
);

/* memory pools for allocations local to processing a region */
extern MEM_POOL MEM_local_region_pool;
extern MEM_POOL MEM_local_region_nz_pool;

extern RID *Current_Rid;

#endif /* lai_INCLUDED */

