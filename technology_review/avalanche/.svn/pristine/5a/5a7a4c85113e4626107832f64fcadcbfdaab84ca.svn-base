/*--------------------------------------------------------------------------------*/
/*-------------------------------- AVALANCHE -------------------------------------*/
/*--- Tracegrind. Transforms IR tainted trace to STP declarations.    parser.h ---*/
/*--------------------------------------------------------------------------------*/

/*
   This file is part of Tracegrind, the Valgrind tool,
   which tracks tainted data coming from the specified file
   and converts IR trace to STP declarations.

   Copyright (C) 2010 Mikhail Ermakov
      mermakov@ispras.ru

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.
*/

#ifndef __PARSER_H
#define __PARSER_H

#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"

struct _fnNode
{
  struct _fnNode* next;
  HWord key;
  Char* data;
};

typedef struct _fnNode fnNode;

struct _offsetPair
{
  ULong first;
  ULong last;
};

typedef struct _offsetPair offsetPair;

Bool parseMask(Char* filename);
Bool parseArgvMask(Char* str, Int* argvFilterUnits);
Bool checkInputOffset(Int curfilenum, ULong offs);
void printInputOffsets (void);
void parseFnName (Char* fnName);
void parseFuncFilterFile (Int fd);

Bool isStandardFunction (Char* objName);

Bool isCPPFunction (Char* fnName);

Bool checkWildcards (Char* fnName);

Bool cmpNames (Char* fnName, Char* checkName);

Bool cutAffixes (Char* fnName);
Bool leaveFnName (Char* fnName);
Bool cutTemplates (Char* fnName);

/* Write used offsets to offsets.log */
Bool storeUsedOffsets(Char *fileName);

#endif
