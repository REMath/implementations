/*--------------------------------------------------------------------------------*/
/*-------------------------------- AVALANCHE -------------------------------------*/
/*--- Tracegrind. Transforms IR tainted trace to STP declarations.    parser.c ---*/
/*--------------------------------------------------------------------------------*/

/*
   This file is part of Tracegrind, the Valgrind tool,
   which tracks tainted data coming from the specified file
   and converts IR trace to STP declarations.

   Copyright (C) 2010 Mikhail Ermakov
      mermakov@ispras.ru
   Copyright (C) 2010 Ildar Isaev
      iisaev@ispras.ru

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

#include "parser.h"
#include "pub_tool_vki.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_hashtable.h"
#include "pub_tool_xarray.h"
#include "pub_tool_oset.h"

extern VgHashTable funcNames;
XArray* inputFilter;

/* This has a pair {index, offsets} for each file */
extern XArray *usedOffsets;
/* This has a pair {index, filename} for each file */
extern XArray *inputFiles;

Bool isStandardFunction (Char* objName)
{
  return ((VG_(strstr) (objName, "/libc-") != NULL) ||
          (VG_(strstr) (objName, "/ld-") != NULL) ||
          (VG_(strstr) (objName, "/libstdc++") != NULL) ||
          (VG_(strstr) (objName, "/libpthread-") != NULL));
}

Bool isCPPFunction (Char* fnName)
{
  return ((VG_(strchr) (fnName, '(') != NULL) ||
          (VG_(strchr) (fnName, '<') != NULL) ||
          (VG_(strchr) (fnName, ':') != NULL));
}

void parseFnName (Char* fnName)
{
  Int l = VG_(strlen) (fnName), i = 0, j = 0;
  Bool nameStarted = False;
  Char* data;
  fnNode* node;
  if (!l) return;
  while (i < l)
  {
    if (fnName[i] == ' ' && !nameStarted)
    {
      i ++;
      continue;
    }
    if (fnName[i] != ' ') nameStarted = True;
    fnName[j ++] = fnName[i ++];
  }
  if (j < i)
  {
    fnName[j] = '\0';
  }
  data = VG_(malloc) ("data", sizeof(Char) * j + 1);
  VG_(memcpy) (data, fnName, j + 1);
  node = VG_(malloc)("fnNode", sizeof(fnNode));
  node->key = hashCode(fnName);
  node->data = data;
  VG_(HT_add_node) (funcNames, node);
}

void parseFuncFilterFile (Int fd)
{
  Int fileLength = VG_(fsize) (fd);
  Char buf[1024];
  Char c;
  Int nameOffset = 0;
  Bool isCommented = False;
  if (fileLength < 2)
  {
    return;
  }
  VG_(memset) (buf, 0, 1024);
  while ((VG_(read) (fd, &c, 1) > 0) && (fileLength -- > 0))
  {
    if (c == '\n')
    {
      if (!isCommented)
      {
        buf[nameOffset] = '\0';
        parseFnName(buf);
      }
      VG_(memset) (buf, 0, nameOffset);
      nameOffset = 0;
      isCommented = False;
    }
    else
    {
      if (nameOffset == 0 && c == '#') isCommented = True;
      else
      {
        buf[nameOffset ++] = c;
      }
    }
  }
}

Bool checkWildcards (Char* fnName)
{
  fnNode* curCheckName;
  Bool tmpNameUpdated = False;
  VG_(HT_ResetIter) (funcNames);
  Char tmpName[1024];
  cutAffixes(fnName);
  while ((curCheckName = (fnNode*) VG_(HT_Next) (funcNames)))
  {
    if (isCPPFunction(curCheckName->data))
    {  
      if (cmpNames(fnName, curCheckName->data)) return True;
    }
    else
    {
      if (!tmpNameUpdated)
      {
        VG_(strcpy) (tmpName, fnName);
        cutTemplates(tmpName);
        leaveFnName(tmpName);
        tmpNameUpdated = True;
      }
      if (cmpNames(tmpName, curCheckName->data)) return True;
    }
  }
  return False;
}

Bool cmpNames (Char* fnName, Char* checkName)
{
  Int sizeFn = VG_(strlen) (fnName);
  Int sizeCh = VG_(strlen) (checkName);
  Int iFn = 0, iCh = 0;
  Char stopWildcardSymbol = False;
  Bool activeWildcard = False;
  Int lastWCardPosition = -1;
  if (sizeCh > sizeFn) return False;
  for (iFn = 0; iFn < sizeFn; iFn ++)
  {
    if (checkName[iCh] == '?')
    {
      if (iCh + 1 == sizeCh) return True;
      stopWildcardSymbol = checkName[++ iCh];
      lastWCardPosition = iCh;
      activeWildcard = True;
      iFn --;
    }
    else 
    {
      if (activeWildcard)
      {
        if (fnName[iFn] == stopWildcardSymbol) { iCh ++; activeWildcard = False; }
        else continue;
      }
      else
      {
        if (fnName[iFn] == checkName[iCh]) { iCh ++; if (iCh == sizeCh) { iFn ++; break; } }
        else if (lastWCardPosition == -1) return False;
        else { iCh = lastWCardPosition; }
      }
    }
  }
  if (iCh == sizeCh && iFn == sizeFn) 
    return True;
  return False;
}

Bool storeUsedOffsets(Char* fileName)
{
  SysRes openRes = 
    VG_(open)(fileName, VKI_O_WRONLY | VKI_O_TRUNC | VKI_O_CREAT,
              VKI_S_IRUSR | VKI_S_IROTH | VKI_S_IRGRP | 
              VKI_S_IWUSR | VKI_S_IWOTH | VKI_S_IWGRP);
  if (sr_isError(openRes))
  {
    return False;
  }
  Int fd = sr_Res(openRes);

  Int previousOffset = -1, i, j;
  Word value;
  for (j = 0; j < VG_(sizeXA) (usedOffsets); j ++)
  {
    OSet *offsetSet = *((OSet **) VG_(indexXA) (usedOffsets, j));
    Char *fileName = * ((Char **) VG_(indexXA) (inputFiles, j));
    VG_(OSetWord_ResetIter) (offsetSet);
    VG_(write) (fd, fileName, VG_(strlen) (fileName));
    while(VG_(OSetWord_Next) (offsetSet, &value)) 
    {
      for (i = previousOffset; i < value - 1; i ++) 
      {
        VG_(write) (fd, "\0", 1);
      }
      VG_(write) (fd, "\1", 1);
      previousOffset = value;
    }
    VG_(OSetWord_Destroy) (offsetSet);
    VG_(free) (fileName);
    VG_(write) (fd, "\n", 1);
  }
  VG_(close) (fd);
  VG_(deleteXA) (inputFiles);
  VG_(deleteXA) (usedOffsets);
  return True;
}

Bool cutTemplates(Char* fnName)
{
  Int a_bracketBalance = 0, i, j = 0, initialI = 0, length = VG_(strlen) (fnName);
  Char tmpName[1024];
  if (((fnName[0] == '<') ? ++ a_bracketBalance : a_bracketBalance) || 
      ((fnName[0] == '>') ? -- a_bracketBalance : a_bracketBalance)) 
  {
    initialI ++;
  }
  for (i = initialI; i < length; i ++)
  {
    if (fnName[i] == '<') 
    {
      if (fnName[i - 1] == '<') { a_bracketBalance --; tmpName[j ++] = '<'; tmpName[j ++] = '<'; }
      else a_bracketBalance ++;
    }
    else if (fnName[i] == '>') 
    {
      if (fnName[i - 1] == '>') { a_bracketBalance ++; tmpName[j ++] = '<'; tmpName[j ++] = '<'; }
      else a_bracketBalance --;
    }  
    else if (!a_bracketBalance)
    {
      tmpName[j ++] = fnName[i];
    }
  }
  for (i = 0; i < length; i ++)
  {
    if (i < j) fnName[i] = tmpName[i];
    else
    {
      fnName[i] = 0;
      break;
    }
  }
  return True;
}

Bool cutAffixes (Char* fnName)
{
  Int length = VG_(strlen) (fnName);
  Int i, j = 0, a_bracketBalance = 0;
#define CONST_SUFFIX_LENGTH 6
  if (length > CONST_SUFFIX_LENGTH)
  {
    if (VG_(strcmp) (fnName + length - CONST_SUFFIX_LENGTH, " const") == 0) 
    {
      *(fnName + length - CONST_SUFFIX_LENGTH) = '\0';
      length -=  CONST_SUFFIX_LENGTH;
    }
  }
#undef CONST_SUFFIX_LENGTH
  for (i = 0; i < length; i ++)
  {
    if (fnName[i] == '(') break;
    switch (fnName[i])
    {
      case '<': a_bracketBalance ++; break;
      case '>': a_bracketBalance --; break;
      case ' ': if (!a_bracketBalance) j = i + 1;
                break;
      default : break;
    }
  }
  if (j != 0 && i == length) return False;
  if (j)
  {
    for (i = j; i < length; i ++)
    {
      fnName[i - j] = fnName[i];
    }
    fnName[i - j] = '\0';
  }
  return True;
}

Bool leaveFnName (Char* fnName)
{
  Char* paramStart = VG_(strchr) (fnName, '(');
  Char* nameStart;
  Int i, initialI;
  if (paramStart == NULL) return False;
  *paramStart = '\0';
  nameStart = VG_(strrchr) (fnName, ':');
  initialI = (nameStart != NULL) ? (nameStart - fnName + 1) : 0;
  for (i = initialI; i < VG_(strlen) (fnName) + 1; i ++)
  {
    fnName[i - initialI] = fnName[i];
    if (fnName[i] == 0) break;
  }
  return True;
}

Bool parseArgvMask(Char* str, Int* argFilterUnits)
{
  Int curOffset = 0;
  Char curStr[16];
  Char** endPtr = VG_(malloc) ("endPtr", sizeof (Char*));
  *endPtr = curStr;
  for (;;)
  {
    if (VG_(isspace) (*str) || (*str == '\0'))
    {
      curStr[curOffset] = '\0';
      curOffset = 0;
      Int index = VG_(strtoll10) (curStr, endPtr);
      if (*endPtr == curStr)
      {
        return False;
      }
      argFilterUnits[index - 1] = 1;
      if (*str == 0)
      {
        break;
      }
      str ++;
    }
    else if (VG_(isdigit) (*str))
    {
      curStr[curOffset ++] = *(str ++);
    }
    else
    {
      return False;
    }
  }
  VG_(free) (endPtr);
  return True;
}

Bool parseMask(Char* filename)
{
  inputFilter = VG_(newXA)(VG_(malloc), "inputFilter", VG_(free), sizeof(XArray*));
  Int fd = sr_Res(VG_(open)(filename, VKI_O_RDWR | VKI_O_CREAT, VKI_S_IRWXU | VKI_S_IRWXG | VKI_S_IRWXO));
  struct vg_stat fileInfo;
  VG_(fstat)(fd,  &fileInfo);
  Long size = fileInfo.size; 
  Char* buf = (Char*) VG_(malloc)("buf", size + 1);
  VG_(read)(fd, buf, size);
  buf[size] = '\0';
  VG_(close)(fd);
  Char* str = buf;
  Char** endptr = &str;
  XArray* curfilter = VG_(newXA)(VG_(malloc), "chunk", VG_(free), sizeof(offsetPair));
  for (;;)
  {
    while (VG_(isspace)(*str))
    {
      while (VG_(isspace)(*str) && (*str != '\n'))
      {
        str++;
      }
      if (*str == '\n')
      {
        VG_(addToXA)(inputFilter, &curfilter);
        curfilter = VG_(newXA)(VG_(malloc), "chunk", VG_(free), sizeof(offsetPair));
        str++;
      }
    }
    Char* str0 = str;
    Long p1 = VG_(strtoll16)(str, endptr);
    if ((*endptr == str0) && (p1 == 0))
    {
      str = *endptr;
      if (*str == '\0')
      {
        break;
      }
      while (VG_(isspace)(*str) && (*str != '\n'))
      {
        str++;
      }
      if (*str != '\n')
      {
        return False;
      }
      else
      {
        VG_(addToXA)(inputFilter, &curfilter);
        curfilter = VG_(newXA)(VG_(malloc), "chunk", VG_(free), sizeof(offsetPair));
        str++;
        continue;
      }
    }
    Long p2 = p1;
    str = *endptr;
    while (VG_(isspace)(*str) && (*str != '\n'))
    {
      str++;
    }
    if (*str == '-')
    {
      str++;
      str0 = str;
      p2 = VG_(strtoll16)(str, endptr);
      if ((*endptr == str0) && (p2 == 0))
      {
        return False;
      }
    }
    offsetPair* newPair = VG_(malloc) ("newPair", sizeof(offsetPair));
    newPair->first = p1;
    newPair->last = p2;
    //VG_(printf)("p1=%x\n", p1);
    //VG_(printf)("p2=%x\n", p2);
    VG_(addToXA)(curfilter, newPair);
    str = *endptr;
    while (VG_(isspace)(*str) && (*str != '\n'))
    {
      str++;
    }
    if (*str == '\n')
    {
      VG_(addToXA)(inputFilter, &curfilter);
      curfilter = VG_(newXA)(VG_(malloc), "chunk", VG_(free), sizeof(offsetPair));
      str++;
    }
    if (*str == '\0')
    {
      break;
    }
  }
  VG_(free)(buf);
  return True;
}

Bool checkInputOffset(Int curfilenum, ULong offs)
{
  if (inputFilter == NULL)
  {
    return True;
  }
  if (curfilenum >= VG_(sizeXA)(inputFilter))
  {
    return False;
  }
  XArray** curfilter = (XArray**) VG_(indexXA)(inputFilter, curfilenum);
  Int i = 0;
  for (; i < VG_(sizeXA)(*curfilter); i++)
  {
    offsetPair* elem = (offsetPair*) VG_(indexXA)(*curfilter, i);
    if ((offs >= elem->first) && (offs <= elem->last)) 
    {
      return True;
    }
  }
  return False;
}

void printInputOffsets()
{
  Int i = 0;
  VG_(printf)("VG_(sizeXA)(inputFilter)=%d\n", (Int) VG_(sizeXA)(inputFilter));
  for (; i < VG_(sizeXA)(inputFilter); i++)
  {
    XArray** curfilter = (XArray**) VG_(indexXA)(inputFilter, i);
    VG_(printf)("VG_(sizeXA)(curfilter)=%d\n", (Int) VG_(sizeXA)(*curfilter));
    Int j = 0;
    for (; j < VG_(sizeXA)(*curfilter); j++)
    {
      offsetPair* elem = (offsetPair*) VG_(indexXA)(*curfilter, j);
      VG_(printf)("p1=%llx ", elem->first);
      VG_(printf)("p2=%llx ", elem->last);
    }
    VG_(printf)("\n");
  }
}
