/*
 * Copyright (C) 2008 Advanced Micro Devices, Inc.  All Rights Reserved.
 */

/*
 *  Copyright (C) 2007, 2008 PathScale, LLC.  All Rights Reserved.
 */

/*
 *  Copyright (C) 2007 QLogic Corporation.  All Rights Reserved.
 */

/*
 * Copyright 2003, 2004, 2005, 2006 PathScale, Inc.  All Rights Reserved.
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

//
// Generate an ISA containing the instructions specified.
/////////////////////////////////////////////////////////
// The instructions are listed by category. The different categories of
// instructions are:
//
//   1. Integer instructions
//   2. FP instructions
//   3. Simulated instructions
//   4. Dummy instructions
//
// Within each category, the instructions are in alphabetical order.
// This arrangement of instructions matches the order in the ISA manual.
/////////////////////////////////////
//
//  $Revision: 1.138 $
//  $Date: 05/11/10 18:45:11-08:00 $
//  $Author: tkong@hyalite.keyresearch $
//  $Source: common/targ_info/isa/x8664/SCCS/s.isa.cxx $

#include <stddef.h>
#include "isa_gen.h"

main ()
{
  ISA_Create( "x8664",

	      /* General-purpose instructions. */
	      "add32",
	      "adc32",
	      "add64",
	      "addx32",
	      "addxx32",
	      "addxxx32",
	      "addx64",
	      "addxx64",
	      "addxxx64",
	      "addi32",
	      "adci32",
	      "addi64",
	      "add128v8",
	      "addx128v8",
	      "addxx128v8",
	      "addxxx128v8",
	      "add128v16",
	      "addx128v16",
	      "addxx128v16",
	      "addxxx128v16",
	      "add128v32",
	      "addx128v32",
	      "addxx128v32",
	      "addxxx128v32",
	      "add128v64",
				"paddusb128",
				"paddusw128",
          "paddsb128",
          "paddsw128",
	      "addx128v64",
	      "addxx128v64",
	      "addxxx128v64",
	      "add64v8",
	      "add64v16",
	      "add64v32",
	      "paddsb",
	      "paddsw",
	      "paddq",
	      "psubsb",
	      "psubsw",
	      "paddusb",
	      "paddusw",
	      "psubusb",
	      "psubusw",
	      "pmullw",
	      "pmulhw",
	      "pmulhuw",
	      "pmulhuw128",
	      "pmaddwd",
	      "and8",
	      "and16",
	      "and32",
	      "andx32",
	      "andxx32",
	      "andxxx32",
	      "and64",
	      "andx64",
	      "andxx64",
	      "andxxx64",
	      "andx8",
	      "andx16",
	      "andxx8",
	      "andxxx8",
	      "andxx16",
	      "andxxx16",
	      "and128v8",
	      "andx128v8",
	      "andxx128v8",
	      "andxxx128v8",
	      "and128v16",
	      "andx128v16",
	      "andxx128v16",
	      "andxxx128v16",
	      "and128v32",
	      "andx128v32",
	      "andxx128v32",
	      "andxxx128v32",
	      "and128v64",
	      "andx128v64",
	      "andxx128v64",
	      "andxxx128v64",
	      "andi32",
	      "andi64",
	      "andn128v8",
	      "andnx128v8",
	      "andnxx128v8",
	      "andnxxx128v8",
	      "andn128v16",
	      "andnx128v16",
	      "andnxx128v16",
	      "andnxxx128v16",
	      "andn128v32",
	      "andnx128v32",
	      "andnxx128v32",
	      "andnxxx128v32",
	      "andn128v64",
	      "andnx128v64",
	      "andnxx128v64",
	      "andnxxx128v64",
	      "call",
	      "icall",
	      "icallx",
	      "icallxx",
	      "icallxxx",
	      "cmp8",
	      "cmpx8",
	      "cmpxx8",
	      "cmpxxx8",
	      "cmp16",
	      "cmpx16",
	      "cmpxx16",
	      "cmpxxx16",
	      "cmp32",
	      "cmpx32",
	      "cmpxx32",
	      "cmpxxx32",
	      "cmp64",
	      "cmpx64",
	      "cmpxx64",
	      "cmpxxx64",
	      "cmpi8",
	      "cmpxr8",
	      "cmpxi8",
	      "cmpxxr8",
	      "cmpxxi8",
	      "cmpxxxr8",
	      "cmpxxxi8",
	      "cmpi16",
	      "cmpxr16",
	      "cmpxi16",
	      "cmpxxr16",
	      "cmpxxi16",
	      "cmpxxxr16",
	      "cmpxxxi16",
	      "cmpi32",
	      "cmpxr32",
	      "cmpxi32",
	      "cmpxxr32",
	      "cmpxxi32",
	      "cmpxxxr32",
	      "cmpxxxi32",
	      "cmpi64",
	      "cmpxr64",
	      "cmpxi64",
	      "cmpxxr64",
	      "cmpxxi64",
	      "cmpxxxr64",
	      "cmpxxxi64",
	      "cmovb",
	      "cmovae",
	      "cmovp",
	      "cmovnp",
	      "cmove",
	      "cmovne",
	      "cmovbe",
	      "cmova",
	      "cmovl",
	      "cmovge",
	      "cmovle",
	      "cmovg",
	      "cmovs",
	      "cmovns",
	      "div32",
	      "div64",
	      "enter",
	      "idiv32",
	      "idiv64",
	      "imul32",
	      "imulx32",
	      "imul64",
	      "imuli32",
	      "imuli64",
	      "imulx64",
	      "mul128v16",
	      "inc8",
	      "dec8",
	      "inc16",
	      "dec16",
	      "inc32",
	      "dec32",
	      "inc64",
	      "dec64",
	      "jb",
	      "jae",
	      "jp",
	      "jnp",
	      "je",
	      "jne",
	      "jbe",
	      "ja",
	      "jl",
	      "jge",
	      "jle",
	      "jg",
	      "jcxz",
	      "jecxz",
	      "jrcxz",
	      "js",
	      "jns",
	      "jmp",
	      "ijmp",
	      "ijmpx",
	      "ijmpxx",
	      "ijmpxxx",
	      "ld64",
	      "ldx64",
	      "ldxx64",
	      "ld64_2m",
	      "ld64_2sse",
	      "lea32",
	      "lea64",
	      "leax32",
	      "leax64",
	      "leaxx32",
	      "leaxx64",
	      "leave",
	      "ldc32",
	      "ldc64",
	      "mul32",
	      "mulx64",
	      "mov32",
	      "mov64",
	      "mov64_m",
          "xchgx8",
          "xchgx16",
          "xchgx32",
          "xchgx64",

	      /* Load without base or index register (offset only) for 64-bit
	         ABI. */
	      "ld32_64_off",
	      "ld64_off",

	      /* Store without base or index register (offset only) for 64-bit
	         ABI. */
	      "store64_off",

	      /* Load without base or index register (offset only) for 32-bit
		 ABI.  (These should really be named *_off to denote
		 offset-only, instead of *_n32 for "n32" ABI.  There is no such
		 thing as x86 "n32" ABI.  These codes correspond to offset-only
		 addressing mode that the compiler uses under 32-bit ABI. */
	      "ld8_32_n32",
	      "ldu8_32_n32",
	      "ld16_32_n32",
	      "ldu16_32_n32",
	      "ld32_n32",
	      "ldss_n32",
	      "ldsd_n32",
	      "ldaps_n32",
	      "ldapd_n32",
              "ldups_n32",
	      "ldupd_n32",
	      "lddqa_n32",
	      "lddqu_n32",
	      "ldlps_n32",
	      "ldlpd_n32",
	      "ldhps_n32",
	      "ldhpd_n32",
	      "ld64_2m_n32",
	      "ld64_2sse_n32",

	      /* Store without base or index register (offset only) for 32-bit
		 ABI.  (These should really be named *_off to denote
		 offset-only, instead of *_n32 for "n32" ABI.  There is no such
		 thing as x86 "n32" ABI.  These codes correspond to offset-only
		 addressing mode that the compiler uses under 32-bit ABI. */
	      "store8_n32",
	      "store16_n32",
	      "store32_n32",
	      "stss_n32",
	      "stsd_n32",
	      "staps_n32",
	      "stapd_n32",
	      "stdqa_n32",
	      "stdqu_n32",
	      "stlps_n32",
	      "sthps_n32",
	      "stlpd_n32",
	      "sthpd_n32",
	      "store64_fm_n32",
	      "store64_fsse_n32",

	      /* Load from %gs segment, without base or index register (offset
	         only) for 32-bit ABI. */
	      "ld32_gs_seg_off",

	      /* Load from %fs segment, without base or index register (offset
	         only) for 64-bit ABI. */
	      "ld64_fs_seg_off",

	      /* 8,16-bit -> 32-bit */
	      "movsbl",
	      "ld8_32",
	      "ldx8_32",
	      "ldxx8_32",
	      "movzbl",
	      "ldu8_32",
	      "ldxu8_32",
	      "ldxxu8_32",
	      "movswl",
	      "ld16_32",
	      "ldx16_32",
	      "ldxx16_32",
	      "movzwl",
	      "ldu16_32",
	      "ldxu16_32",
	      "ldxxu16_32",
	      /* 8,16-bit -> 64-bit */
	      "movsbq",
	      "ld8_64",
	      "ldx8_64",
	      "ldxx8_64",
	      "ld8_64_off",
	      "movzbq",
	      "ldu8_64",
	      "ldxu8_64",
	      "ldxxu8_64",
	      "ldu8_64_off",
	      "movswq",
	      "ld16_64",
	      "ldx16_64",
	      "ldxx16_64",
	      "ld16_64_off",
	      "movzwq",
	      "ldu16_64",
	      "ldxu16_64",
	      "ldxxu16_64",
	      "ldu16_64_off",
	      /* 32-bit -> 64-bit */
	      "movslq",
	      "ld32_64",
	      "ldx32_64",
	      "ldxx32_64",
	      "ld32",
	      "ldx32",
	      "ldxx32",
	      "movzlq",

	      "neg32",
	      "neg64",
	      "not32",
	      "not64",
	      "or8",
	      "or16",
	      "or32",
	      "orx32",
	      "orxx32",
	      "orxxx32",
	      "or64",
	      "orx64",
	      "orxx64",
	      "orxxx64",
	      "orx8",
	      "orx16",
	      "orxx8",
	      "orxxx8",
	      "orxx16",
	      "orxxx16",
	      "or128v8",
	      "orx128v8",
	      "orxx128v8",
	      "orxxx128v8",
	      "or128v16",
	      "orx128v16",
	      "orxx128v16",
	      "orxxx128v16",
	      "or128v32",
	      "orx128v32",
	      "orxx128v32",
	      "orxxx128v32",
	      "or128v64",
	      "orx128v64",
	      "orxx128v64",
	      "orxxx128v64",
	      "ori32",
	      "ori64",
	      "popl",
	      "popq",
	      "pushl",
	      "pushq",
	      "ret",
	      "reti",
	      "ror8",
	      "ror16",
	      "ror32",
	      "ror64",
	      "rori8",
	      "rori16",
	      "rori32",
	      "rori64",
	      "rol8",
	      "rol16",
	      "rol32",
	      "rol64",
	      "roli8",
	      "roli16",
	      "roli32",
	      "roli64",
	      "prefetch",
	      "prefetchw",
	      "prefetcht0",
	      "prefetcht1",
	      "prefetchnta",
	      "prefetchx",
	      "prefetchxx",
	      "prefetchwx",
	      "prefetchwxx",
	      "prefetcht0x",
	      "prefetcht0xx",
	      "prefetcht1x",
	      "prefetcht1xx",
	      "prefetchntax",
	      "prefetchntaxx",
	      "setb",
	      "setae",
	      "setp",
	      "setnp",
	      "sete",
	      "setne",
	      "setbe",
	      "seta",
	      "setl",
	      "setge",
	      "setle",
	      "setg",
	      "store8",
	      "storex8",
	      "storexx8",
	      "store16",
	      "storex16",
	      "storexx16",
	      "store32",
	      "storex32",
	      "storexx32",
	      "store64",
	      "storex64",
	      "storexx64",
	      "store64_fm",
	      "store64_fsse",
	      "storenti32",
	      "storentix32",
	      "storentixx32",
	      "storenti64",
	      "storentix64",
	      "storentixx64",
	      "storenti128",
	      "sar32",
	      "sar64",
	      "sari32",
	      "sari64",
	      "shl32",
	      "shld32",
	      "shldi32",
	      "shrd32",
	      "shrdi32",
	      "shl64",
	      "shli32",
	      "shli64",
	      "shr32",
	      "shr64",
	      "shri32",
	      "shri64",
	      "sub32",
	      "sbb32",
	      "sub64",
	      "subx32",
	      "subx64",
	      "subxx32",
	      "subxxx32",
	      "subxx64",
	      "subxxx64",
	      "subi32",
	      "sbbi32",
	      "subi64",
	      "sub128v8",
	      "subx128v8",
	      "subxx128v8",
	      "subxxx128v8",
	      "sub128v16",
	      "subx128v16",
	      "subxx128v16",
	      "subxxx128v16",
	      "sub128v32",
	      "subx128v32",
	      "subxx128v32",
	      "subxxx128v32",
	      "sub128v64",
	      "subx128v64",
	      "subxx128v64",
	      "subxxx128v64",
	      "sub64v8",
	      "sub64v16",
	      "sub64v32",
	      "test32",
	      "testx32",
	      "testxx32",
	      "testxxx32",
	      "test64",
	      "testx64",
	      "testxx64",
	      "testxxx64",
	      "testi32",
	      "testi64",
	      "xor8",
	      "xor16",
	      "xor32",
	      "xorx32",
	      "xorxx32",
	      "xorxxx32",
	      "xor64",
	      "xorx64",
	      "xorxx64",
	      "xorxxx64",
	      "xorx8",
	      "xorx16",
	      "xorxx8",
	      "xorxxx8",
	      "xorxx16",
	      "xorxxx16",
	      "xor128v8",
	      "xorx128v8",
	      "xorxx128v8",
	      "xorxxx128v8",
	      "xor128v16",
	      "xorx128v16",
	      "xorxx128v16",
	      "xorxxx128v16",
	      "xor128v32",
	      "xorx128v32",
	      "xorxx128v32",
	      "xorxxx128v32",
	      "xor128v64",
	      "xorx128v64",
	      "xorxx128v64",
	      "xorxxx128v64",
	      "xori32",
	      "xori64",
	      "fxor128v32",
	      "fxorx128v32",
	      "fxorxx128v32",
	      "fxorxxx128v32",
	      "fxor128v64",	      
	      "fxorx128v64",	      
	      "fxorxx128v64",	      
	      "fxorxxx128v64",	      
	      "xorps",
	      "xorpd", 
	      
	      /* floating point instructions. */
	      "addsd",
	      "addss",
	      "addxsd",
	      "addxss",
	      "addxxsd",
	      "addxxxsd",
	      "addxxss",
	      "addxxxss",
	      "faddsub128v32",
	      "faddsubx128v32",
	      "faddsubxx128v32",
	      "faddsubxxx128v32",
	      "faddsub128v64",
	      "faddsubx128v64",
	      "faddsubxx128v64",
	      "faddsubxxx128v64",
	      "fadd128v32",
	      "faddx128v32",
	      "faddxx128v32",
	      "faddxxx128v32",
	      "fadd128v64",
	      "faddx128v64",
	      "faddxx128v64",
	      "faddxxx128v64",
	      "fhadd128v32",
	      "fhaddx128v32",
	      "fhaddxx128v32",
	      "fhaddxxx128v32",
	      "fhadd128v64",
	      "fhaddx128v64",
	      "fhaddxx128v64",
	      "fhaddxxx128v64",
	      "fand128v32",
	      "fandx128v32",
	      "fandxx128v32",
	      "fandxxx128v32",
	      "fand128v64",
	      "fandx128v64",
	      "fandxx128v64",
	      "fandxxx128v64",
	      "fandn128v64",
	      "fandnx128v64",
	      "fandnxx128v64",
	      "fandnxxx128v64",
	      "andps",
	      "andpd",
	      "andnps",
	      "andnpd",
	      "for128v32",
	      "forx128v32",
	      "forxx128v32",
	      "forxxx128v32",
	      "for128v64",
	      "forx128v64",
	      "forxx128v64",
	      "forxxx128v64",
	      "orps",
	      "orpd",
	      "comisd",
	      "comixsd",
	      "comixxsd",
	      "comixxxsd",
	      "comiss",
	      "comixss",
	      "comixxss",
	      "comixxxss",
	      "cmpss",
	      "cmpsd",
	      "cmpps",
	      "cmppd",
	      "cmpneqps",
	      "cmpeq128v8",
	      "cmpeq128v16",
	      "cmpeq128v32",
	      "cmpeqx128v8",
	      "cmpeqx128v16",
	      "cmpeqx128v32",
	      "cmpeqxx128v8",
	      "cmpeqxx128v16",
	      "cmpeqxx128v32",
	      "cmpeqxxx128v8",
	      "cmpeqxxx128v16",
	      "cmpeqxxx128v32",
	      "cmpgt128v8",
	      "cmpgt128v16",
	      "cmpgt128v32",
	      "cmpgtx128v8",
	      "cmpgtx128v16",
	      "cmpgtx128v32",
	      "cmpgtxx128v8",
	      "cmpgtxx128v16",
	      "cmpgtxx128v32",
	      "cmpgtxxx128v8",
	      "cmpgtxxx128v16",
	      "cmpgtxxx128v32",
	      "pcmpeqb",
	      "pcmpeqw",
	      "pcmpeqd",
	      "pcmpgtb",
	      "pcmpgtw",
	      "pcmpgtd",
	      "fmovsldup",
	      "fmovshdup",
	      "fmovddup",
	      "fmovsldupx",
	      "fmovshdupx",
	      "fmovddupx",
	      "fmovsldupxx",
	      "fmovshdupxx",
	      "fmovddupxx",
	      "fmovsldupxxx",
	      "fmovshdupxxx",
	      "fmovddupxxx",

	      // sign-extend dword in %eax to quad in %edx:%eax
	      "cltd",
	      // sign-extend quad in %rax to octuple in %rdx:%rax
	      "cqto",

	      /* fp -> fp */
	      "cvtss2sd",
	      "cvtsd2ss",
	      "cvtsd2ss_x",
	      "cvtsd2ss_xx",
	      "cvtsd2ss_xxx",
	      /* int -> fp */
	      "cvtsi2sd",
	      "cvtsi2sd_x",
	      "cvtsi2sd_xx",
	      "cvtsi2sd_xxx",
	      "cvtsi2ss",
	      "cvtsi2ss_x",
	      "cvtsi2ss_xx",
	      "cvtsi2ss_xxx",
	      "cvtsi2sdq",
	      "cvtsi2sdq_x",
	      "cvtsi2sdq_xx",
	      "cvtsi2sdq_xxx",
	      "cvtsi2ssq",
	      "cvtsi2ssq_x",
	      "cvtsi2ssq_xx",
	      "cvtsi2ssq_xxx",
	      /* fp -> int */
	      "cvtss2si",
	      "cvtsd2si",
	      "cvtss2siq",
	      "cvtsd2siq",
	      "cvttss2si",
	      "cvttsd2si",
	      "cvttss2siq",
	      "cvttsd2siq",
	      /* vector cvt */
	      "cvtdq2pd",
	      "cvtdq2ps",
	      "cvtps2pd",
	      "cvtpd2ps",
	      "cvtps2dq",
	      "cvttps2dq",
	      "cvtpd2dq",
	      "cvttpd2dq",
	      "cvtdq2pd_x",
	      "cvtdq2ps_x",
	      "cvtps2pd_x",
	      "cvtpd2ps_x",
	      "cvtps2dq_x",
	      "cvttps2dq_x",
	      "cvttpd2dq_x",
	      "cvtdq2pd_xx",
	      "cvtdq2ps_xx",
	      "cvtps2pd_xx",
	      "cvtpd2ps_xx",
	      "cvtps2dq_xx",
	      "cvttps2dq_xx",
	      "cvttpd2dq_xx",
	      "cvtdq2pd_xxx",
	      "cvtdq2ps_xxx",
	      "cvtps2pd_xxx",
	      "cvtpd2ps_xxx",
	      "cvtps2dq_xxx",
	      "cvttps2dq_xxx",
	      "cvttpd2dq_xxx",
	      "cvtpi2ps",
	      "cvtps2pi",
	      "cvttps2pi",
	      "cvtpi2pd",
	      "cvtpd2pi",
	      "cvttpd2pi",
	      /* misc */
	      "ldsd",
	      "ldsdx",
	      "ldsdxx",
	      "ldss",
	      "ldssx",
	      "ldssxx",
	      "lddqa",
	      "lddqu",
	      "ldlps",
	      "ldhps",
	      "ldlpd",
	      "ldhpd",
	      "stdqa",
	      "stdqu",
	      "stlps",
	      "sthps",
	      "stlpd",
	      "storelpd",
	      "sthpd",
	      "stntpd",
	      "stntps",
	      "storent64_fm",
	      "lddqax",
	      "lddqux",
	      "ldlpsx",
	      "ldhpsx",
	      "ldlpdx",
	      "ldhpdx",
	      "stdqax",
	      "stntpdx",
	      "stntpsx",
	      "stdqux",
	      "stlpsx",
	      "sthpsx",
	      "stlpdx",
	      "sthpdx",
	      "lddqaxx",
	      "lddquxx",
	      "ldlpsxx",
	      "ldhpsxx",
	      "ldlpdxx",
	      "ldhpdxx",
	      "ldaps",
	      "ldapsx",
	      "ldapsxx",
	      "ldapd",
	      "ldapdx",
	      "ldapdxx",
	      "ldups",
	      "ldupd",
	      "stdqaxx",
	      "stntpdxx",
	      "stntpsxx",
	      "stdquxx",
	      "stlpsxx",
	      "sthpsxx",
	      "stlpdxx",
	      "sthpdxx",
	      "staps",
	      "stapsx",
	      "stapsxx",
	      "stapd",
	      "stapdx",
	      "stapdxx",
	      "stups",
	      "stupd",
	      "maxsd",
	      "maxss",
	      "fmax128v32",
	      "fmaxx128v32",
	      "fmaxxx128v32",
	      "fmaxxxx128v32",
	      "fmax128v64",
	      "fmaxx128v64",
	      "fmaxxx128v64",
	      "fmaxxxx128v64",
	      "max128v16",
	      "max128v8",
	      "maxx128v16",
	      "maxx128v8",
	      "maxxx128v16",
	      "maxxx128v8",
	      "maxxxx128v16",
	      "maxxxx128v8",
	      "max64v8",
	      "max64v16",
	      "min128v16",
	      "min128v8",
	      "minx128v16",
	      "minx128v8",
	      "minxx128v16",
	      "minxx128v8",
	      "minxxx128v16",
	      "minxxx128v8",
	      "min64v8",
	      "min64v16",
	      "minsd",
	      "minss",
	      "fmin128v32",
	      "fminx128v32",
	      "fminxx128v32",
	      "fminxxx128v32",
	      "fmin128v64",
	      "fminx128v64",
	      "fminxx128v64",
	      "fminxxx128v64",
	      "movx2g64",
	      "movx2g",
	      "movg2x64",
	      "movg2x",
	      "movsd",
	      "movss",
	      "movdq",
	      "movapd",
	      "movaps",
	      "movq2dq",
	      "movdq2q",
	      "divsd",
	      "divxsd",
	      "divxxsd",
	      "divxxxsd",
	      "divss",
	      "divxss",
	      "divxxss",
	      "divxxxss",
	      "fdiv128v32",
	      "fdivx128v32",
	      "fdivxx128v32",
	      "fdivxxx128v32",
	      "fdiv128v64",
	      "fdivx128v64",
	      "fdivxx128v64",
	      "fdivxxx128v64",
	      "mulsd",
	      "mulss",
	      "fmul128v32",
	      "fmulx128v32",
	      "fmulxx128v32",
	      "fmulxxx128v32",
	      "fmul128v64",
	      "fmulx128v64",
	      "fmulxx128v64",
	      "fmulxxx128v64",
	      "mulxsd",
	      "mulxss",
	      "mulxxsd",
	      "mulxxxsd",
	      "mulxxss",
	      "mulxxxss",
	      "subsd",
	      "subss",
	      "subxsd",
	      "subxss",
	      "subxxsd",
	      "subxxxsd",
	      "subxxss",
	      "subxxxss",
	      "fsub128v32",
	      "fsubx128v32",
	      "fsubxx128v32",
	      "fsubxxx128v32",
	      "fsub128v64",
	      "fsubx128v64",
	      "fsubxx128v64",
	      "fsubxxx128v64",
	      "fhsub128v32",
	      "fhsubx128v32",
	      "fhsubxx128v32",
	      "fhsubxxx128v32",
	      "fhsub128v64",
	      "fhsubx128v64",
	      "fhsubxx128v64",
	      "fhsubxxx128v64",

	      "stss",
	      "stntss",
	      "stssx",
	      "stntssx",
	      "stssxx",
	      "stntssxx",
	      "stsd",
	      "stntsd",
	      "stsdx",
	      "stntsdx",
	      "stsdxx",
	      "stntsdxx",
	      "rcpss",
	      "frcp128v32",
	      "sqrtsd",
	      "sqrtss",
	      "rsqrtss",
	      "fsqrt128v32",
	      "frsqrt128v32",
	      "fsqrt128v64",
	      "punpcklwd",
	      "punpcklbw",
	      "punpckldq",
	      "punpckhbw",
	      "punpckhwd",
	      "punpckhdq",
	      "punpckl64v8",
	      "punpckl64v16",
	      "punpckl64v32",
	      "packsswb",
	      "packssdw",
	      "packuswb",
	      "packsswb128",
	      "packssdw128",
	      "packuswb128",
	      "punpckhbw128",
	      "punpckhwd128",
	      "punpckhdq128",
	      "punpckhqdq",
	      "punpcklbw128",
	      "punpcklwd128",
	      "punpckldq128",
	      "punpcklqdq",
	      "pavgb128",
	      "pavgw128",
	      "pshufd",
	      "pshufw",
	      "pshuflw",
	      "pshufhw",
	      "pslldq",
	      "psllw",
	      "pslld",
	      "psllq",
	      "psrlw",
	      "psrld",
	      "psrlq",
	      "psraw",
	      "psrad",
	      "psllw_mmx",
	      "pslld_mmx",
	      "psrlw_mmx",
	      "psrld_mmx",
	      "psraw_mmx",
	      "psrad_mmx",
	      "pand_mmx",
	      "pandn_mmx",
          "pand128",
          "pandn128",
					"por128",
	      "por_mmx",
	      "pxor_mmx",
	      "unpckhpd",
	      "unpckhps",
	      "unpcklpd",
	      "unpcklps",
	      "shufpd",
	      "shufps",
	      "movhlps",
	      "movlhps",
	      "psrldq",
	      "psrlq128v64",
	      "subus128v16",
	      "pavgb",
	      "pavgw",
	      "psadbw",
	      "psadbw128",
	      "pextrw64",
	      "pextrw128",
	      "pinsrw64",
	      "pinsrw128",
	      "pmovmskb",
	      "pmovmskb128",
	      "movi32_2m",
	      "movi64_2m",
	      "movm_2i32",
	      "movm_2i64",
	      "pshufw64v16",
	      "movmskps",
	      "movmskpd",
	      "maskmovdqu",
	      "maskmovq",
              "extrq",
              "insertq",

              /* Fence instructions. */
	      "mfence",
	      "lfence",
	      "sfence",

              /* Pseudo instructions. */
	      "asm",
	      "intrncall",
	      "spadjust",
	      "savexmms",

              /* Instruction to zero out integer registers */
	      "zero32",
	      "zero64",

              /* Instruction to zero out fp registers */
	      "xzero32",
	      "xzero64",
	      "xzero128v32",
	      "xzero128v64",

	      /* x87 floating-point instructions */
	      "fadd",
	      "faddp",
	      "flds",      // load float -> st0
	      "flds_n32",  // load float -> st0
	      "fldl",      // load double -> st0
	      "fldl_n32",  // load double -> st0
	      "fldt",      // load ext double -> st0
	      "fldt_n32",  // load ext double -> st0, w/o index or base
	      "fld",
	      "fst",
	      "fstp",
	      "fstps",     // store st0 -> float
	      "fstps_n32", // store st0 -> float
	      "fstpl",     // store st0 -> double
	      "fstpl_n32", // store st0 -> double
	      "fstpt",     // store st0 -> ext double
	      "fstpt_n32", // store st0 -> ext double, w/o index or base
	      "fsts",     // store st0 -> float
	      "fsts_n32", // store st0 -> float
	      "fstl",     // store st0 -> double
	      "fstl_n32", // store st0 -> double
	      "fxch",
	      "fmov",
	      "fsub",
	      "fsubr",
	      "fsubp",
	      "fsubrp",
	      "fmul",
	      "fmulp",
	      "fdiv",
	      "fdivp",
	      "fdivr",
	      "fdivrp",
	      "fucomi",
	      "fucomip",
	      "fchs",    // reverse the sign bit of ST0
	      "frndint", // round the contents of ST0 to an integer
	      "fnstcw",  // store x87 control-word
	      "fldcw",   // load x87 control-word
	      "fistps",  // st0 -> short int
	      "fistpl",  // st0 -> int
	      "fists",   // st0 -> short int
	      "fistl",   // st0 -> int
	      "fistpll", // st0 -> long and long long
	      "filds",   // short int -> st0
	      "fildl",   // int -> st0
	      "fildll",  // long long -> st0
	      "fldz",    // push value +0.0 onto the x87 register stack
	      "fabs",
	      "fsqrt",
	      "fcmovb",
	      "fcmovbe",
	      "fcmovnb",
	      "fcmovnbe",
	      "fcmove",
	      "fcmovne",
	      "fcmovu",
	      "fcmovnu",
	      "fcos",
	      "fsin",

	      /* sse instructions */
	      "cmpeqps",
	      "cmpeqpd",
	      "cmpltpd",
	      "cmplepd",
	      "cmpgtpd",
	      "cmpgepd",
	      "cmpneqpd",
	      "cmpnltpd",
	      "cmpnlepd",
	      "cmpngtpd",
	      "cmpngepd",
	      "cmpordpd",
	      "cmpunordpd",
	      "cmpltps",
	      "cmpleps",
	      "cmpunordps",
	      "cmpnltps",
	      "cmpnleps",
	      "cmpordps",
	      "cmpeqss",
	      "cmpltss",
	      "cmpless",
	      "cmpunordss",
	      "cmpneqss",
	      "cmpnltss",
	      "cmpnless",
	      "cmpordss",
	      "cmpeqsd",
	      "cmpltsd",
	      "cmplesd",
	      "cmpunordsd",
	      "cmpneqsd",
	      "cmpnltsd",
	      "cmpnlesd",
	      "cmpordsd",
	      "emms",
				"clflush",
	      "stmxcsr",
	      "ldmxcsr",

	      /* sse3 instruction */
	      "fisttps",  // st0 -> short int
	      "fisttpl",  // st0 -> int
	      "fisttpll", // st0 -> long long

	      /* instructions to support -mcmodel=medium */
	      "movabsq",
	      "store8_abs",
	      "store16_abs",
	      "store32_abs",
	      "store64_abs",
	      "ld8_abs",
	      "ld16_abs",
	      "ld32_abs",
	      "ld64_abs",

				/* sse4_1 instructions*/
				"pblendw",
				"blendpd",
				"blendps",
				"pblendvb",
				"blendvpd",
				"blendvps",
				"roundpd",
				"roundsd",
				"roundps",
				"roundss",
				"pcmpeqq",
				"pmovsxbw",
				"pmovsxbd",
				"pmovsxbq",
				"pmovsxwd",
				"pmovsxwq",
				"pmovsxdq",
				"pmovzxbw",
				"pmovzxbd",
				"pmovzxbq",
				"pmovzxwd",
				"pmovzxwq",
				"pmovzxdq",
				"packusdw",
				"dppd",
				"dpps",
				"mpsadbw",
				"pmuldq",
				"pmulld",
				"pextrb",
				"pextrd",
				"pextrq",
				"extractps",
				"pinsrb",
				"pinsrd",
				"pinsrq",
				"insertps",
				"pmaxsb",
				"pmaxsd",
				"pmaxuw",
				"pmaxud",
				"pminsb",
				"pminsd",
				"pminuw",
				"pminud",
				"phminposuw",
				"movntdqa",
				"ptest",

          /* sse4_2 instructions */
          "pcmpistri",  
          "pcmpistrm",
					"pcmpgtq",
          "pcmpestri",
          "pcmpestrm",
          "crc32b",
          "crc32w",
          "crc32l",
          "crc32q",
					"popcntl",
					"popcntq",

					/* sss3 instructions*/
					"phaddw128",
					"phaddd128",
					"phaddsw128",
					"phaddw",
					"phaddd",
					"phaddsw",
					"phsubw128",
					"phsubd128",
					"phsubsw128",
					"phsubw",
					"phsubd",
					"phsubsw",
					"pabsb128",
					"pabsw128",
					"pabsd128",
					"pabsb",
					"pabsw",
					"pabsd",
					"pmaddubsw128",
					"pmaddubsw",
					"pmulhrsw128",
					"pmulhrsw",
					"palignr128",
					"palignr",
					"pshufb128",
					"pshufb",

	      /* instructions to support Open MP. */
	      "lock_add32",
	      "lock_adc32",
	      "lock_add64",
	      "lock_cmpxchg32",
	      "lock_cmpxchg64",
	      "lock_and32",
	      "lock_and64",
	      "lock_or32",
	      "lock_or64",
	      "lock_xor32",
	      "lock_xor64",
	      "lock_sub32",
	      "lock_sub64",

	      /* more lock instructions */
	      "lock_add8",
	      "lock_add16",
	      "lock_cmpxchg8",
	      "lock_cmpxchg16",
	      "lock_and8",
	      "lock_and16",
	      "lock_or8",
	      "lock_or16",
	      "lock_xor8",
	      "lock_xor16",
	      "lock_sub8",
	      "lock_sub16",
	      "lock_xadd8",
	      "lock_xadd16",
	      "lock_xadd32",
	      "lock_xadd64",

	      /* miscellaneous */
	      "bsf32",
	      "bsf64",
	      "bsr32",
	      "bsr64",

	      /* Dummy instructions. */
	      "begin_pregtn",
	      "end_pregtn",
	      "bwd_bar",
	      "fwd_bar",
	      "label",
	      "nop",
	      "noop",
              "swp_start",
              "swp_stop",

	      /* END */
	      NULL);
}
