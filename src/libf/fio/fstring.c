/*

  Copyright (C) 2000, 2001, Silicon Graphics, Inc.  All Rights Reserved.

   Path64 is free software; you can redistribute it and/or modify it
   under the terms of the GNU Lesser General Public License as published by
   the Free Software Foundation version 2.1

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



#pragma ident "@(#) libf/fio/fstring.c	92.3	08/27/99 17:38:17"

#if HAVE_ALLOCA_H
#include <alloca.h>
#endif
#include <stdlib.h>
#include <string.h>

/*
 *	Fortran character string handling routines for compiler-generated
 *	code.
 */

#define BLANK	((int) ' ')
#define	NUMBLNKS 128

static char *blanks =
	"                                "  /*  32 */
	"                                "  /*  64 */
	"                                "  /*  96 */
	"                                "  /* 128 */
;

/*
 *	b_pad	Pad Fortran string with blanks.
 *
 *	Algorithm:  use memset() and assume it's reasonably optimized.
 */

void
b_pad(	char	*str,
	int	len )
{
	memset (str, BLANK, len);

	return;
}

/*
 *	s_cat	Concatenate Fortran strings.
 *
 *	Concatenate an arbitrary number of strings.  If the length of
 *	the concatenated strings is shorter than the destination, then
 *	pad with blanks; if longer, then truncate.  Fortran semantics
 *	require full expression evaluation before assignment so an
 *	intermediate buffer is used in case the same (sub)string appears
 *	on both sides of the assignment and would otherwise be overwritten
 *	before concatenation.
 *
 *	Strings may overlap and zero-length strings are allowed (per the
 *	Fortran 90 standard).
 *
 *	Algorithm:  use memcpy() and assume it's reasonably optimized.
 *		Build final result in intermediate buffer and use memcpy()
 *		again to move it to the final destination.  If the result
 *		is shorter than destination then use memset() to blank
 *		fill remainder.
 *
 *      Other optimizations to be considered:
 *		1) An intermediate buffer is only necessary in a small
 *		   number of cases.  Some sort of check could possibly
 *		   conditionally eliminate it, but may not be worth the
 *		   the trouble.
 *		2) Inline memcpy/memset
 *		3) And of course, have the compiler generate the concatenation
 *		   inline.
 */

void
s_cat(	char	*dest,		/* Destination of concatenation */
	char	*src[],		/* String(s) to be concatenated */
	int	slen[],		/* ... and their length(s)	*/
	int	*num,		/* Number of strings		*/
	int	dlen )		/* Length of destination	*/
{
	register int	cnt;
	register int	i;
	register int	len;
	char		*buf;

	buf	= alloca(dlen);
	cnt	= *num;
	len	= 0;

	for (i = 0; i < cnt; i++) {
		register int	tcnt;

		tcnt	= ((dlen - len) <= slen[i]) ? (dlen - len) : slen[i];

		if (tcnt < 0)	/* If destination is full, stop */
			break;

		(void) memcpy (&buf[len], src[i], tcnt);

		len	= len + tcnt;
	}

	(void) memcpy(dest, buf, len);

	memset (&dest[len], BLANK, dlen - len);

	return;
}

/*
 *	s_copy	Copy Fortran string.
 *
 *	Copy string2 to string1.  If string2 is shorter than string1, then
 *	pad with blanks.  If string2 is longer than string1, then truncate.
 *
 *	Strings may overlap and zero-length strings are allowed (per Fortran
 *	90).
 *
 *	Algorithm:  use memmove() and assume it's reasonably optimized.  If
 *		source is shorter than destination, then use memset() to
 *		blank fill remainder.
 *
 *      Other optimizations to be considered:
 *		1) Inline memmove/memset
 *		2) Special-case short strings, duplicate strings (s1 == s2),
 *		   and zero-length strings.
 *		3) And of course, have the compiler generate the move inline.
 */

void
s_copy(	char	*s1,
	char	*s2,
	int	l1,
	int	l2 )
{
	register int	len;

	len	= l1 - l2;

	if (len <= 0)	/* If length of destination <= length of source */
		(void) memmove(s1, s2, l1);	/* Copy as much as will fit */
	else {
		(void) memmove(s1, s2, l2);	/* Copy source */
		memset (s1 + l2, BLANK, len);	/* Pad remainder with blanks */
	}

	return;
}

/*
 *	s_cmp	Compare Fortran strings.
 *
 *	Returns:  0 if strings are equal
 *		 <0 if string 1 is less than string 2
 *		 >0 if string 1 is greater than string 2
 *
 *	If the lengths of the strings are unequal, comparison occurs as
 *	if the shorter string were padded with blanks.
 *
 *	Zero-length strings are allowed (per Fortran 90).
 *
 *	Algorithm:  use memcmp() and assume it's reasonably optimized.  If
 *		substrings are equal, compare remnant with preset string of
 *		blanks.
 *
 *      Other optimizations to be considered:
 *		1) Inline memmove
 *		2) Special-case short strings, duplicate strings (s1 == s2),
 *		   and zero-length strings.
 *		3) And of course, have the compiler generate the comparisons
 *		   inline.
 */

int
s_cmp(	char	*s1,
	char	*s2,
	int	l1,
	int	l2 )
{
	register int	chnk;
	register int	len;
	register int	ret;

	len	= (l1 < l2) ? l1 : l2;

	/* Compare the common substring with memcmp */

	ret	= memcmp(s1, s2, len);

	if ((ret != 0) || (l1 == l2))
		goto scmp_exit;

	if (l1 < l2) {		/* s1 is shorter than s2 */
		s1	= blanks;
		s2	= s2 + len;
		len	= l2 - l1;	/* Length of remnant */
	} else {		/* s2 is shorter than s1 */
		s1	= s1 + len;
		s2	= blanks;
		len	= l1 - l2;	/* Length of remnant */
	}

	chnk	= NUMBLNKS;

	do {

		if (len < chnk)
			chnk	= len;

		len	= len - chnk;

		ret	= memcmp(s1, s2, chnk);

		if (l1 < l2)		/* s1 is shorter than s2 */
			s2	= s2 + chnk;
		else
			s1	= s1 + chnk;

	} while (ret == 0 && len > 0);

scmp_exit:
	return (ret);
}
