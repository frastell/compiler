/*
 * Copyright 2004, 2005, 2006 PathScale, Inc.  All Rights Reserved.
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

/* $Header: /home/bos/bk/kpro64-pending/libU77/getcwd_.c 1.6 04/12/21 14:58:06-08:00 bos@eng-25.internal.keyresearch.com $ */
 /*
 * Get pathname of current working directory.
 *
 * calling sequence -32bit:
 *	character*128 path
 *	integer *4 getcwd, ierr
 *	ierr = getcwd(path)
 * calling sequence -64bit:
 *	character*128 path
 *	integer *8 getcwd, ierr
 *	ierr = getcwd(path)
 * or alternatively (-32bit and -64bit):
 *      character*128 path
 *	call getcwd(path)
 * where:
 *	path will receive the pathname of the current working directory.
 *	ierr will be non-zero if successful
 */

#include <errno.h>
#include <unistd.h>
#include <sys/param.h>
#ifndef	MAXPATHLEN
#define MAXPATHLEN	128
#endif
#include "externals.h"

#include "pathf90_libU_intrin.h"

pathf90_i4
pathf90_getcwd(char *path, pathf90_i4 *status, int len)
{
	char	*p;
	char	pathname[MAXPATHLEN];
	pathf90_i4 junk;
	status = (0 == status) ? (&junk) : status;

	/*
	 * Bug 3349: ensure that getcwd is used.
	 * Never use getwd as fallback.
	 */
	p = getcwd(pathname, sizeof(pathname));

	b_char(pathname, path, len);
	if (p)
		return(*status = 0);
	else
		return(*status = errno);
}
