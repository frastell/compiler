/*
 * Copyright (C) 2007, 2008, 2009 PathScale, LLC.  All Rights Reserved.
 */

/*
 *  Copyright (C) 2006, 2007. QLogic Corporation. All Rights Reserved.
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


/*
 * OPTIONS that are not simple enough to handle in the table
 * are done by hand in these routines.
 */

#include <string.h>
#include <stdlib.h>
#include <stamp.h>
#include "string_utils.h"
#include "options.h"
#include "option_seen.h"
#include "option_names.h"
#include "lang_defs.h"
#include "errors.h"
#include "opt_actions.h"
#include "file_names.h"
#include "get_options.h"
#include "phases.h"
#include "run.h"
#include "targets.h"

#ifndef TARG_MIPS
int endian = UNDEFINED; /* defined in options table */
#endif

void
set_defaults (void)
{
	int flag;
	/* handle PSC_CC environment variable */
	char *psc_cc = getenv("PSC_CC");
	if (psc_cc != NULL && !is_toggled(ansi)) {
		/* value not set yet */
		if (strcmp(psc_cc, "-ansi") == 0) {
			toggle(&ansi,STRICT_ANSI);
			prepend_option_seen (O_ansi);
		}
	}

	{
	  /* QA wants way to turn off this check via environment var */
	  char *ir_version_check = getenv("COMPILER_IR_VERSION_CHECK");
	  if (ir_version_check != NULL) {
		if (strcmp(ir_version_check, "off") == 0) {
			flag = add_string_option(O_DEBUG_, "ir_version_check=off");
			/* prepend so comes before user option */
			prepend_option_seen(flag);
		}
	  }
	}
	if (endian == UNDEFINED) {
#ifdef TARG_MIPS
        if (is_target_arch_MIPS()) {
            /* Default to little-endian -JMB */
            toggle(&endian, ENDIAN_LITTLE);
            prepend_option_seen(O_EL);
        } else {
#endif
#ifdef LITTLE_ENDIAN_HOST
            toggle(&endian, ENDIAN_LITTLE);
#else
            toggle(&endian, ENDIAN_BIG);
            prepend_option_seen(O_EB);
#endif
#ifdef TARG_MIPS
        }
#endif
	}

	prepend_option_seen(O_usef90);

	if (ansi == UNDEFINED) {
		toggle(&ansi,EXTENDED_ANSI);
	}

	prepend_option_seen(O_cpp_fortran90);
	prepend_option_seen(O_cpp_fortran);
	prepend_option_seen(O_cpp_assembly);
	prepend_option_seen(O_prelink);
#ifndef __sun
	prepend_option_seen(O_demangle);
#endif
	if (shared == UNDEFINED && abi == ABI_IA32) {
		toggle(&shared,NON_SHARED);
#ifndef KEY
		prepend_option_seen(O_non_shared);
#endif
	}
#ifdef TARG_MIPS
	else if (is_target_arch_MIPS() &&
             shared == UNDEFINED &&
             (abi == ABI_N32 || abi == ABI_64))
    {
		prepend_option_seen(O_fpic);
	}
#endif
	if (!is_toggled(isstatic)) {
		toggle(&isstatic,1);
		prepend_option_seen(O_automatic);
	}

#ifdef KEY
	// Make -cpp the default for Fortran.  Bug 4243.
	if (!is_toggled(use_ftpp)) {
		toggle(&use_ftpp, 0);
	}

#endif
}


static int
get_olevel_flag (int olevel)
{
	switch (olevel) {
	case 0: return O_O0;
	case 1: return O_O1;
	case 2: return O_O2;
	case 3: return O_O3;
	default: return O_Unrecognized;
	}
}

/* replace -O* with O0 */
void
turn_down_opt_level (int new_olevel, char *msg)
{
	int flag;
	int new_flag;
	if (fullwarn) warning("%s", msg);
	flag = get_olevel_flag(olevel);
	new_flag = get_olevel_flag(new_olevel);
	if (option_was_seen(O_O))
		replace_option_seen (O_O, new_flag);
	else if (option_was_seen(flag))
		replace_option_seen (flag, new_flag);
	else
		internal_error("driver didn't find -O flag");
	olevel = new_olevel;
}

static void
turn_off_ipa (char *msg)
{
	int flag;
	warning ("%s", msg);
	ipa = FALSE;
	/* remove all ipa flags from option_seen list */
	FOREACH_OPTION_SEEN(flag) {
		if (flag == O_ipa)
			set_option_unseen(flag);
		else if (flag == O_IPA)
			set_option_unseen(flag);
		else if (is_derived_option (flag)
		    && get_derived_parent(flag) == O_IPA_)
			set_option_unseen(flag);
	}
}

static void
turn_off_tirex (string msg)
{
  int flag;
  warning (msg);
  tirex = FALSE;
  /* remove all tirex flags from option_seen list */
  FOREACH_OPTION_SEEN(flag) {
    if (flag == O_X)
      set_option_unseen(flag);
  }
}


void
add_special_options (void)
{
	int flag;
	buffer_t buf;
	char *s;
	boolean undefined_olevel_flag = FALSE; 

	/* Hack for F90 -MDupdate. We need to pass the MDupdate to mfef95, because we don't
	 * have an integrated pre-processor. I can't figure out a better way to do this, given
	 * the architecture of the phase generator. 
	 * R. Shapiro, 2/26/97
	 */
	add_phase_for_option(O_MDupdate,P_f90_fe);
	add_phase_for_option(O_MDtarget,P_f90_fe);

        add_phase_for_option(O_D, P_cppf90_fe);
        add_phase_for_option(O_U, P_cppf90_fe);
        add_phase_for_option(O_E, P_cppf90_fe);
        add_phase_for_option(O_P, P_cppf90_fe);

	if (use_ftpp == TRUE) {
		/* ftpp means pass defines directly to mfef95,
		 * and since not using gcc we have to pass some options
		 * that are otherwise implicit. */
		flag = add_string_option(O_D, "_LITTLE_ENDIAN");
		prepend_option_seen (flag);
    		flag = add_string_option(O_D, "__LONG_MAX__=9223372036854775807L");
		prepend_option_seen (flag);
		prepend_option_seen (O_cpp_nonansi);
		if (keep_flag) {
			add_phase_for_option (O_keep, P_cppf90_fe);
		}
	}

	if (option_was_seen(O_traditional)
		&& !option_was_seen(O_traditional_cpp)) 
	{
		/* pass -traditional to both gfe and cpp */
		add_phase_for_option(O_traditional, P_c_gfe);
		add_phase_for_option(O_traditional, P_cplus_gfe);
#ifdef PATH64_ENABLE_GNU_FRONTEND
#ifdef KEY
		add_phase_for_option(O_traditional, P_spin_cc1);
		add_phase_for_option(O_traditional, P_spin_cc1plus);
#endif // KEY
#endif // PATH64_ENABLE_GNU_FRONTEND
	}

#if defined(TARG_IA32)
    if(is_target_arch_MIPS()) {
        flag = add_string_option(O_D, "__NO_MATH_INLINES");
        prepend_option_seen (flag);
    }
#endif

#ifdef KEY
	// Pass -fopenmp instead of -mp to GNU 4.2 or later C/C++ front-end.
	// Bug 12824.
	if (mpkind == NORMAL_MP &&
	    (invoked_lang == L_cc ||
	     invoked_lang == L_CC)) {
	  set_option_unseen(O_mp);
	  set_option_unseen(O_openmp);
	  add_option_seen(O_fopenmp);
	}
#endif

#ifndef KEY	// Bug 4406.
	if (mpkind == CRAY_MP) {
		Process_Cray_Mp();
	}
	else if (mpkind == NORMAL_MP || auto_parallelize) {
		Process_Mp();
	}
#endif

#ifndef KEY	// Bug 7263.
        if (auto_parallelize && ipa) {
                flag = add_new_option("-IPA:array_summary");
                add_phase_for_option(flag, P_ipl);
                prepend_option_seen (flag);
        }
#endif

	if ((mpkind == NORMAL_MP 
#ifndef KEY // bug 8107
	     || auto_parallelize
#endif
	    ) && !Disable_open_mp) {
#ifdef KEY /* bug 14510 */
		flag = add_string_option(O_D, "_OPENMP=200505");
#else
		flag = add_string_option(O_D, "_OPENMP=199810");
#endif
		prepend_option_seen (flag);
	}

	if (olevel == UNDEFINED) {
		olevel = default_olevel;
		if (olevel == UNDEFINED) {
			/* if no default, use -O0 */
			olevel = 0;
		}
		flag = get_olevel_flag(olevel);
		prepend_option_seen (flag);
		// fix for bug 447
		undefined_olevel_flag = TRUE;
	}
	if (!nostdinc) {
		/* mips only: add -I path for CC */
                if (abi != ABI_I64 && abi != ABI_I32 && abi != ABI_IA32) {
                  flag = add_string_option(O_I__, 
                              concat_strings(get_phase_dir(P_include),"/CC"));
                  set_language_for_option (flag, L_CC);
                  add_option_seen (flag);
                }
	}
	if (!is_toggled(gnum)) {
		/* set gnum default */
		if (abi == ABI_RAG32) {
			/* be compatible with ucode */
			if (shared == NON_SHARED) {
				toggle(&gnum,8);
			} else {
				toggle(&gnum,0);
			}
		} else {
			toggle(&gnum,8);
		}
		sprintf(buf, "%d", gnum);
		flag = add_string_option(O_G__, buf);
		prepend_option_seen(flag);
	}

	/* Set default optimization to -O0 when compiling with -g.
	 * We leave ipa alone because mixing -ipa with -g is illegal
	 * and generates a separate error later on.
	 * NOTE: The above sentence is not correct any more, as we now
	 * allow "-g -ipa" for SiCortex 5069. This flag set still turns
	 * down opt level to -O0 if not set explicitly.
	 */
	if (undefined_olevel_flag == TRUE && glevel > 1) {
		turn_down_opt_level(0, "-g changes optimization to -O0 since no optimization level is specified");
	}

#ifdef KEY
	/* Turn off inlining when compiling -O0.  We definitly want
	 * this off when compiling with -g -O0, but we don't want
	 * -g to change the generated code so we leave it off always.
	 * See bugs 1917 and 7595.
	 */
	/* Instead of skipping inline at -O0 we now run it with -INLINE:none
	 * so it will remove unused static inline declarations.
	 */
	/* if (olevel == 0 && inline_t == UNDEFINED) */
	  /* inline_t = FALSE; */
#endif

#ifdef KEY /* Bug 5367 */
        /* In the SGI world, -g3 says to emit crippled debug info for use
	 * with optimized code. In the GNU/Pathscale world, -g3 says to emit
	 * additional debug info for C preprocessor macros, so changing -g to
	 * -g3 just because the optimization level is high makes no sense. In
	 * addition, when the language is Fortran, putting predefined C
	 * preprocessor macros into the preprocessor output causes trouble.
	 */
	if (invoked_lang == L_f90 && option_was_seen(O_g3)) {
	  glevel = 2;
	  replace_option_seen (O_g3, O_g2);
	}
#else
	if (olevel >= 2 && glevel == 2) {
		glevel = 3;
		if (option_was_seen (O_g))
			replace_option_seen (O_g, O_g3);
		if (option_was_seen (O_g2))
			replace_option_seen (O_g2, O_g3);
	}
#endif /* KEY Bug 5367 */

	if (option_was_seen(O_S) && ipa == TRUE) {
		turn_off_ipa ("-IPA -S combination not allowed, replaced with -S");
	}
	if (option_was_seen(O_S) && tirex == TRUE) {
	  turn_off_tirex ("-X -S combination not allowed, replaced with -S");
	}
#ifdef IPA_PROFILING_O3_NOT_COEXIST
	if (instrumentation_invoked == TRUE) {
	    if (ipa == TRUE) {
		inline_t = FALSE;
		turn_off_ipa ("-fb_create requires no -IPA");
	    }
	    if (olevel > 2)
		turn_down_opt_level (2, "-fb_create conflicts with -Ofast/-O3; changing to -O2");
	}
#endif
	if (Gen_feedback && olevel > 0) {
		turn_down_opt_level(0, "-fbgen conflicts with -O; changing to -O0");
	}
	if (Gen_feedback && ipa == TRUE) {
		turn_off_ipa ("-IPA -fbgen combination not allowed, replaced with -fbgen");
	}
#if 0
	/* Disable for SiCortex 5069. */
	/* Fix for BUG 451 */
	if (glevel > 1 && ipa == TRUE) {
		turn_off_ipa ("-IPA -g combination not allowed, replaced with -g");
	}
#endif
	if (ipa == TRUE) {
#ifdef KEY // bug 8130
            if (option_was_seen (O_fprofile_arcs))
	      error ("IPA not supported with -fprofile-arcs");
	    if (option_was_seen (O_ftest_coverage))
	      error ("IPA not supported with -ftest-coverage");
#endif
#ifdef FAT_WHIRL_OBJECTS
	    /* Merge phase options for be and ipl. */
	    if (olevel <= 1 || source_kind == S_O)
		flag = add_string_option(O_PHASE_, "c:i");
	    else if (olevel == 2 || source_kind == S_N)
		flag = add_string_option(O_PHASE_, "w:c:p:i");
	    else 
		flag = add_string_option(O_PHASE_, "l:w:c:p:i");
#else
	    if (olevel <= 1)
		flag = add_string_option (O_PHASE_, "i");
	    else
		flag = add_string_option (O_PHASE_, "p:i");
#endif //FAT_WHIRL_OBJECTS
	} else {
	    /*
	     * Determine which back end phase(s) need to be run.
	     *
	     *			-O0/-O1	-O2		-O3
	     *			===========================
	     *		.B,.I:	cg	wopt/cg		lno/wopt/cg
	     *		.N:	cg	wopt/cg		wopt/cg
	     *		.O:	cg	cg		cg
	     */
	    if (source_kind == S_O)
		warning("compiles of WOPT-generated .O files will usually fail due to missing state information");
	    if (olevel <= 1 || source_kind == S_O)
		flag = add_string_option(O_PHASE_, "c");
	    else if (olevel == 2 || source_kind == S_N)
		flag = add_string_option(O_PHASE_, "w:c");
	    else 
		flag = add_string_option(O_PHASE_, "l:w:c");
	}
	prepend_option_seen (flag);

	if (abi == ABI_N32 || abi == ABI_64) {
#ifndef KEY
        	set_dsm_options ();
#endif
	}

	if (option_was_seen(O_ar) && outfile == NULL) {
	   error("-ar option requires archive name to be specified with -o option");
	}
	
	if (! keep_flag && last_phase != P_be) {
		/* if going thru asm and not keeping .s file,
		 * then don't print extra notes and source */
		flag = add_string_option(O_LIST_, "source=off:notes=off");
		prepend_option_seen (flag);
	}
#ifdef TARG_X8664
        /*make the -VHO:rotate default */
	if(is_target_arch_X8664()) {
	    if(olevel >= 2) {
	        flag = add_string_option(O_VHO_, "rotate");
                prepend_option_seen (flag);   
	    }
	}
#endif // TARG_X8664
}

