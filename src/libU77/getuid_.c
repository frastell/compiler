/*
 * Copyright 2003, 2004, 2005, 2006 PathScale, Inc.  All Rights Reserved.
 */

/*

  Copyright (C) 1999-2001, Silicon Graphics, Inc.  All Rights Reserved.

  This program is free software; you can redistribute it and/or modify it
  under the terms of version 2.1 of the GNU Lesser General Public License
  as published by the Free Software Foundation.

  This program is distributed in the hope that it would be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  Further, any
  license provided herein, whether implied or otherwise, is limited to 
  this program in accordance with the express provisions of the 
  GNU Lesser General Public License.  

  Patent licenses, if any, provided herein do not apply to combinations 
  of this program with other product or programs, or any other product 
  whatsoever.  This program is distributed without any warranty that the 
  program is delivered free of the rightful claim of any third person by 
  way of infringement or the like.  

  See the GNU Lesser General Public License for more details.

  You should have received a copy of the GNU General Public License along
  with this program; if not, write the Free Software Foundation, Inc., 59
  Temple Place - Suite 330, Boston MA 02111-1307, USA.

*/

/* $Header: /home/bos/bk/kpro64-pending/libU77/getuid_.c 1.6 04/12/21 14:58:07-08:00 bos@eng-25.internal.keyresearch.com $ */
/*
 *
 * get user id
 *
 * calling sequence:
 *	integer getuid, uid
 *	uid = getuid()
 * where:
 *	uid will be the real user id
 */
#include <sys/types.h>
#include <unistd.h>
#ifndef KEY
#include <sgidefs.h>
#endif

#ifdef KEY /* Bug 1683 */

#include "pathf90_libU_intrin.h"

pathf90_i4
pathf90_getuid(void)

#else

extern int32_t
getuid_(void)

#endif /* KEY Bug 1683 */
{
	return((int32_t)getuid());
}
