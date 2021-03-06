/*
 * Copyright (C) 2008 PathScale, LLC.  All Rights Reserved.
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
 * Module: tcon2f.c
 * $Revision$
 * $Date$
 * $Author$
 * $Source$
 *
 * Revision history:
 *  27-Apr-95 - Original Version
 *
 * Description:
 *
 *    See tcon2f.h for a description of the exported functions and 
 *    variables.
 *
 * ====================================================================
 * ====================================================================
 */

#define __STDC_FORMAT_MACROS
#include <inttypes.h>
#ifdef _KEEP_RCS_ID
/*REFERENCED*/
static char *rcs_id = "$Source$ $Revision$";
#endif

#include "whirl2f_common.h"
#include "tcon2f.h"
#if HAVE_ALLOCA_H
#include <alloca.h>
#endif


/*---------------------- Hidden utilities ---------------------*/
/*-------------------------------------------------------------*/
  
static char *
Remove_Trailing_Zero_Fraction(char *strbase)
{
   /* Expect the input to be of the form: "d.dddde+dd", where a '-' may 
    * occur in place of the '+', or the '+' could be omitted.  We view the
    * 'e' as any letter.
    */
   INT last, i;

   /* Get to the first digit from the right, which is non-zero.
    */
   for (last = 0; strbase[last] != '\0'; last++);
   for (i = last-1; strbase[i] == '0'; i--);

   /* Remove any unnecesary exponent part and the trailing zeros in the
    * fractional part.
    */
   if (strbase[i] < '0' || strbase[i] > '9')
   {
      while (strbase[i] < '0' || strbase[i] > '9') i--;
      while (strbase[i] == '0') i--;
      if (strbase[i] == '.')
      {
	 strbase[i+1] = '0';
	 last = i+2;
      }
      else
      {
	 last = i+1;
      }
   }
   else
   {
      INT j, remove_to;

      while (strbase[i] >= '0' && strbase[i] <= '9') i--; /* skip exp digits */
      while (strbase[i] < '0' || strbase[i] > '9') i--; /* skip exp letters */
      remove_to = i;

      while (strbase[i] == '0') i--; /* skip zero digits in the fraction */
      if (strbase[i] == '.')
	 i += 1;

      /* Move exponent part up till just after the non-zero fractional part
       */
      for (j = remove_to+1; j < last; j++)
	 strbase[++i] = strbase[j];
      last = i+1;
   }
   strbase[last] = '\0';

   return strbase;
} /* Remove_Trailing_Zero_Fraction */


static char *
TCON2F_append_string_char(char *str, char ch)
{
  BOOL escape;
  char escaped_ch;
  
  switch (ch)
  {
  case '\n':
     escaped_ch = 'n';
     escape = TRUE;
     break;
  case '\t':
     escaped_ch = 't';
     escape = TRUE;
     break;
  case '\b':
     escaped_ch = 'b';
     escape = TRUE;
     break;
  case '\r':
     escaped_ch = 'r';
     escape = TRUE;
     break;
  case '\f':
     escaped_ch = 'f';
     escape = TRUE;
     break;
  case '\v':
     escaped_ch = 'v';
     escape = TRUE;
     break;
  case '\\':
     escaped_ch = '\\';
     escape = TRUE;
     break;
  case '\'':
     escaped_ch = '\'';
     escape = TRUE;
     break;
  default: 
     escaped_ch = ch;
     escape = FALSE;
     break;
  }
  if (escape)
     *str++ = '\\';
  *str++ = escaped_ch;

  return str;
} /* TCON2F_append_string_char */


void 
TCON2F_Append_String_Const(TOKEN_BUFFER tokens, 
			   const char  *orig_str, 
			   INT32        strlen)
{
   const char *str_base;
   char       *str;
   INT32       stridx;

   str_base = str = (char * )alloca(2*strlen + 3); /* "'", orig_str, "'", and "\0" */
   *(str++) = '\'';
   for (stridx = 0; stridx < strlen; stridx++)
      str = TCON2F_append_string_char(str, orig_str[stridx]);
   while (str[-1] == '\0') str--;
   *(str++) = '\'';
   *(str++) = '\0';
   Append_Token_String(tokens, str_base);
} /* TCON2F_Append_String_Const */


/*---------------------- Exported functions -------------------*/
/*-------------------------------------------------------------*/

void 
TCON2F_hollerith(TOKEN_BUFFER tokens, TCON tvalue)
{
   /* Translates the given Hollerith constant into Fortran representation.
    * A hollerith constant cannot be split into substrings.
    */
   const char *strbase;
   char       *str;
   INT32       strlen;

   ASSERT_DBG_WARN(TCON_ty(tvalue) == MTYPE_STR,
		   (DIAG_W2F_UNEXPECTED_BTYPE, 
		    MTYPE_name(TCON_ty(tvalue)), "TCON2F_hollerith"));

   strlen = Targ_String_Length(tvalue);
   strbase = Targ_String_Address(tvalue);
   str = (char *) alloca(strlen + 16);
   sprintf(str, "%dH%s", strlen, strbase);
   Append_Token_String(tokens, str);
} /* TCON2F_hollerith */

   
void 
TCON2F_translate(TOKEN_BUFFER tokens, TCON tvalue, BOOL is_logical)
{
   /* Translates the given TCON to a Fortran representation.  Since
    * the tcon itself does not tell us, we must rely on the context
    * to inform us whether or not a integer constant is a logical
    * value or not.
    */
   char *strbase;
   char *str;
   INT32 max_strlen, strlen, stridx;
   
   if (is_logical &&
       MTYPE_type_class(TCON_ty(tvalue)) & MTYPE_CLASS_INTEGER)
   {
      /* Treat it as regular integral constant, unless it has
       * value 0 or 1.
       */
      if (Targ_To_Host(tvalue) == 0LL)
	 Append_Token_String(tokens, ".FALSE.");
      else if  (Targ_To_Host(tvalue) == 1LL)
	 Append_Token_String(tokens, ".TRUE.");
      else
	 is_logical = FALSE;
   }
   else /* Only integral values can be treated as boolean */
      is_logical = FALSE; 

   if (!is_logical)
   {
      switch (TCON_ty(tvalue))
      {
      case MTYPE_STR:
	 max_strlen = (Get_Maximum_Linelength()*2)/3;
	 strlen = Targ_String_Length(tvalue);
	 strbase = Targ_String_Address(tvalue);
	 if (max_strlen > 0 && max_strlen < strlen)
	 {
	    /* We need to split the string constant into substrings */
	    str = (char *) alloca(max_strlen + 1);
	    while (strlen > max_strlen)
	    {
	       for (stridx = 0; stridx < max_strlen; stridx++)
		  str[stridx] = strbase[stridx];
	       str[stridx] = '\0';
	       strbase = &strbase[stridx];
	       strlen -= max_strlen;
	       TCON2F_Append_String_Const(tokens, str, max_strlen);
	       Append_Token_String(tokens, "//"); /* Concatenation */
	    }
	 }
	 TCON2F_Append_String_Const(tokens, strbase, strlen);
	 break;

      case MTYPE_I1:
      case MTYPE_I2:
      case MTYPE_I4:
	 Append_Token_String(tokens, Targ_Print("%1d", tvalue));
	 break;

      case MTYPE_I8:
	 Append_Token_String(tokens, Targ_Print("%1"PRId64"_8", tvalue));
	 break;
      
      case MTYPE_U1:
      case MTYPE_U2:
      case MTYPE_U4:
	 Append_Token_String(tokens, Targ_Print("%1u", tvalue));
	 break;

      case MTYPE_U8:
	 Append_Token_String(tokens, Targ_Print("%1llu_8", tvalue));
	 break;

      case MTYPE_F4:
	 str = Targ_Print("%.10e", tvalue);
	 strbase = Remove_Trailing_Zero_Fraction(str);
	 if (str = strchr(strbase, 'd'))
	    *str = 'E';
	 Append_Token_String(tokens, strbase);
	 break;

      case MTYPE_F8:
	 str = Targ_Print("%.20e", tvalue);
	 strbase = Remove_Trailing_Zero_Fraction(str);
	 if (str = strchr(strbase, 'E')) /* due to bug in targ_const.h */
	    *str = 'D';
	 else if (str = strchr(strbase, 'd'))
	    *str = 'D';
	 else
	    strbase = (char *)Concat2_Strings(strbase, "D00");
	 Append_Token_String(tokens, strbase);
	 break;

      case MTYPE_FQ:
      case MTYPE_F16:
	 str = Targ_Print(NULL, tvalue);
	 strbase = Remove_Trailing_Zero_Fraction(str);
	 if (str = strchr(strbase, 'E')) /* due to bug in targ_const.h */
	    *str = 'Q';
	 else if (str = strchr(strbase, 'd'))
	    *str = 'Q';
	 else
	    strbase = (char *)Concat2_Strings(strbase, "Q00");
	 Append_Token_String(tokens, strbase);
	 break;
	 
      case MTYPE_C4:
      case MTYPE_C8:
      case MTYPE_CQ:
      case MTYPE_C16:
	 Append_Token_Special(tokens, '(');
	 TCON2F_translate(tokens, Extract_Complex_Real(tvalue), FALSE);
	 Append_Token_Special(tokens, ',');
	 TCON2F_translate(tokens, Extract_Complex_Imag(tvalue), FALSE);
	 Append_Token_Special(tokens, ')');
	 break;

      default:
	 /* Only expression nodes should be handled here */
	 ASSERT_DBG_WARN(FALSE, (DIAG_W2F_UNEXPECTED_BTYPE, 
				 MTYPE_name(TCON_ty(tvalue)),
				 "TCON2F_translate"));
	 Append_Token_String(tokens, "<aTCON>");
	 break;
      } /* switch */
   } /* if */
} /* TCON2F_translate */
