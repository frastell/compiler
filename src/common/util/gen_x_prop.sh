#!/bin/sh
#
#
#  Copyright (C) 2000, 2001 Silicon Graphics, Inc.  All Rights Reserved.
#  Copyright (C) 2010, PathScale Inc. All Rights Reserved
#
#  Path64 is free software; you can redistribute it and/or modify it
#  under the terms of the GNU General Public License as published by
#  the Free Software Foundation; either version 2, or (at your option)
#  any later version.
#
#  Path64 is distributed in the hope that it will be useful, but WITHOUT
#  ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
#  or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
#  License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with Path64; see the file COPYING.  If not, write to the Free
#  Software Foundation, 51 Franklin Street, Fifth Floor, Boston, MA
#  02110-1301, USA.
#
#  Special thanks goes to SGI for their continued support to open source
#
#

### ====================================================================
### ====================================================================
### Module: gen_x_prop.sh
### $Revision$
### $Date$
### $Author$
### $Source$
### Revision history:
###   27-Feb-92 - Original version
###
### Synopsis:   gen_x_prop.sh - Create an instantiation of simple properties
###                              onto a base type.  This is something you
###                              really can't do with the CPP.
###
### Usage:      sh gen_x_prop TYPE PREFIX ID_ACCESS [INCLUDE...]
###
###             Creates the files type_prop.h and type_prop.cxx that
###             implement a module for manipulating very simple bit
###             sets over the univers of objects of the given TYPE.
###             See util/x_prop.h for documentation of the specific
###             functions generated.
###
###             The arguments are:
###
###             TYPE  -     is the complete name of the underlying
###                         type.  For structure types, you probably
###                         need to include the final *, as they are
###                         typically passed by reference.  For types
###                         not passed by reference, such as indices
###                         and the rare single word structure, omit
###                         the final *. TYPE is the actual complete
###                         declaration of the base type parameters of
###                         the new functions.
###
###             PREFIX -    A single identifier to be prepended to the
###                         name of the new type and newly created
###                         functions.
###
###             ID_ACCESS - is an expression to access (must be able
###                         to be both and L and an R value) the
###                         unique id number of "x", an expression
###                         of the underlying type.
###
###             INCLUDE   - is a file name to be included in the generated
###                         .cxx file.  The above expressions all have
###                         to be parsed and their components defined.
###                         INCLUDES have to include all the .h files
###                         necessary for this.  In particular, it
###                         will probably include xxx.h and memory.h
###
### ====================================================================
### ====================================================================

###
### Parse the arguments:
###
BASE_TYPE="$1"
shift
PREFIX="$1"
shift
ID_ACCESS="$1"
shift

###
### Make the derived names:
###
rev='$Revision$'

L_PREFIX=`echo $PREFIX | tr [:upper:] [:lower:]`

H_RCS_ID="${L_PREFIX}_prop_rcs_id"
ID_ACCES="${PREFIX}_id"
TYPE="${PREFIX}_PROP"
CREATE="${PREFIX}_PROP_Create"
SET="${PREFIX}_PROP_Set"
RESET="${PREFIX}_PROP_Reset"
GET="${PREFIX}_PROP_Get"
UNIOND="${PREFIX}_PROP_UnionD"
INTERSECT="${PREFIX}_PROP_Intersection_Is_NonEmpty"



###
### Make the names of the output files:
###
H_FILE="${L_PREFIX}_prop.h"
C_FILE="${L_PREFIX}_prop.cxx"


###
### Generate the .h file:
###
echo "/* Constructed by gen_x_prop $rev"		>$H_FILE
echo " */"						>>$H_FILE
echo "#ifndef ${L_PREFIX}_prop_included"		>>$H_FILE
echo "#define ${L_PREFIX}_prop_included"		>>$H_FILE
echo "#define _X_PROP_TYPE_ $TYPE"			>>$H_FILE
echo "#define _X_BASE_TYPE_ $BASE_TYPE"			>>$H_FILE
echo "#define _X_RCS_ID_ $H_RCS_ID"			>>$H_FILE
echo "#define _X_PROP_CREATE_ $CREATE"			>>$H_FILE
echo "#define _X_PROP_SET_ $SET"			>>$H_FILE
echo "#define _X_PROP_RESET_ $RESET"			>>$H_FILE
echo "#define _X_PROP_GET_ $GET"			>>$H_FILE
echo "#define _X_PROP_UNIOND_ $UNIOND"			>>$H_FILE
echo "#define _X_PROP_INTERSECTION_IS_NONEMPTY_ $INTERSECT"            \
                                                        >>$H_FILE
echo "#define _X_PROP_LOCAL_BASE_TYPE_ ${PREFIX}_PROP_LOCAL_BASE_TYPE_"          \
							>>$H_FILE
echo "#include " \""x_prop.h"\"				>>$H_FILE
echo "#undef _X_PROP_TYPE_"				>>$H_FILE
echo "#undef _X_BASE_TYPE_"				>>$H_FILE
echo "#undef _X_RCS_ID_"				>>$H_FILE
echo "#undef _X_PROP_CREATE_"				>>$H_FILE
echo "#undef _X_PROP_SET_"				>>$H_FILE
echo "#undef _X_PROP_RESET_"				>>$H_FILE
echo "#undef _X_PROP_GET_"				>>$H_FILE
echo "#undef _X_PROP_UNIOND_"				>>$H_FILE
echo "#undef _X_PROP_LOCAL_BASE_TYPE_"			>>$H_FILE
echo "#undef _X_PROP_INTERSECTION_IS_NONEMPTY_"		>>$H_FILE
echo "#endif"						>>$H_FILE

###
### Generate the .cxx file:
###

echo "/* Constructed by gen_x_prop $rev"		>$C_FILE
echo " */"						>>$C_FILE
for INCLUDE in "$@"; do printf '#include "%s"\n' "$INCLUDE" >>$C_FILE; done
# Old CSH stuff leaving around for no particular reason
#foreach INCLUDE ($*)
#  echo "#include " \""$INCLUDE"\"			>>$C_FILE
#end
echo "#define _X_PROP_TYPE_ $TYPE"			>>$C_FILE
echo "#define _X_BASE_TYPE_ $BASE_TYPE"			>>$C_FILE
echo "#define _X_id_(x) $ID_ACCESS"			>>$C_FILE
echo "#define _X_PROP_CREATE_ $CREATE"			>>$C_FILE
echo "#define _X_PROP_SET_ $SET"			>>$C_FILE
echo "#define _X_PROP_RESET_ $RESET"			>>$C_FILE
echo "#define _X_PROP_GET_ $GET"			>>$C_FILE
echo "#define _X_PROP_UNIOND_ $UNIOND"			>>$C_FILE
echo "#define _X_PROP_INTERSECTION_IS_NONEMPTY_ $INTERSECT"            \
                                                        >>$C_FILE
echo "#define _X_PROP_LOCAL_BASE_TYPE_ ${PREFIX}_PROP_LOCAL_BASE_TYPE_"          \
							>>$C_FILE
echo "#include " \""x_prop.c"\"				>>$C_FILE
