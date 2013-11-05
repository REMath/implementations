/*--------------------------------------------------------------------------------*/
/*-------------------------------- AVALANCHE -------------------------------------*/
/*--- Tracegrind. Transforms IR tainted trace to STP declarations.   tg_main.c ---*/
/*--------------------------------------------------------------------------------*/

/*
   This file is part of Tracegrind, the Valgrind tool,
   which tracks tainted data coming from the specified file
   and converts IR trace to STP declarations.

   Copyright (C) 2009-2011 Ildar Isaev
      iisaev@ispras.ru
   
   Copyright (C) 2010-2011 Mikhail Ermakov
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

#include "pub_tool_basics.h"
#include "pub_tool_options.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_hashtable.h"
#include "pub_tool_xarray.h"
#include "pub_tool_oset.h"
#include "pub_tool_clientstate.h"
#include "pub_tool_aspacemgr.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_vki.h"
#include "pub_tool_vkiscnums.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_machine.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_stacktrace.h"
#include "libvex_ir.h"

#include <avalanche.h>

#include "buffer.h"
#include "copy.h"
#include "parser.h"

#if defined(VGP_arm_linux) || defined(VGP_x86_linux)
#define PTR_SIZE "32"
#define PTR_FMT "%08lx"
#elif defined(VGP_amd64_linux)
#define PTR_SIZE "64"
#define PTR_FMT "%016lx"
#endif

#define PERM_R_W VKI_S_IRUSR | VKI_S_IROTH | VKI_S_IRGRP | \
                 VKI_S_IWUSR | VKI_S_IWOTH | VKI_S_IWGRP

//#define TAINTED_TRACE_PRINTOUT
//#define CALL_STACK_PRINTOUT

Addr curIAddr;
Bool enableFiltering = False;

Bool inTaintedBlock = False;

Bool suppressSubcalls = False;

VgHashTable funcNames;

Char* diFunctionName;
Char* diVarName;

Char* checkArgvList;
Char* tempDir;
Char* hostTempDir;

Bool newSB;
IRSB* printSB;

/* We can't use curfilenum, since one file can be opened several
     times. Using {file_name, offsets} map will be costly, that's why
     we'll make two arrays and use indices in both as a link key. */
XArray *inputFiles;
XArray *usedOffsets;

Int fdfuncFilter = -1;

Bool inputFilterEnabled;

VgHashTable taintedMemory;
VgHashTable taintedRegisters;
VgHashTable taintedTemps = NULL;

VgHashTable startAddr;

extern VgHashTable fds;
extern HChar* curfile;
extern Int cursocket;
extern Int curfilenum;
extern ULong curoffs;
extern ULong cursize;

VgHashTable tempSizeTable;
sizeNode* curNode;

Int socketfd;
Bool dumpChunkSize;

ULong start = 0;

Bool isRead = False;
Bool isOpen = False;
extern Bool curDeclared;
extern Bool addTaintedSocket;
extern Bool isRecv;
extern Bool isMap;
Bool checkPrediction = False;
extern Bool sockets;
extern Bool datagrams;
Bool replace = False;
static Int socketsNum = 0;
static Int socketsBoundary;
static replaceData* replace_data;
Bool dumpPrediction = False;
Bool divergence = False;
Bool* prediction;
Bool* actual;

UWord curblock = 0;

Int fdtrace;
Int fddanger;
extern VgHashTable inputfiles;
extern UShort port;
extern UChar ip1, ip2, ip3, ip4;

Int depth = 0;
Int invertdepth = 0;
Bool noInvertLimit = False;
Int curdepth;

Int memory = 0;
Int registers = 0;
UInt curvisited;

Bool checkDanger = False;

Bool protectArgName = False;

extern 
IRExpr* adjustSize(IRSB* sbOut, IRTypeEnv* tyenv, IRExpr* arg);

extern
void instrumentWrTmpCCall_External(IRSB* sbOut, IRStmt* clone, 
                                   IRExpr* value0, IRExpr* value1, 
                                   IRExpr* value2, IRExpr* value3);

extern
void instrumentWrTmpLongBinop_External(IRSB* sbOut, IRStmt* clone, 
                                       IRExpr* value1, IRExpr* value2);

static
Bool getFunctionName(Addr addr, Bool onlyEntry, Bool showOffset)
{
  Bool continueFlag = False;
  if (onlyEntry)
  {
    continueFlag = VG_(get_fnname_if_entry) (addr, diFunctionName, 1024);
  }
  else if (showOffset)
  {
    continueFlag = VG_(get_fnname_w_offset) (addr, diFunctionName, 1024);
  }
  else
  {
    continueFlag = VG_(get_fnname) (addr, diFunctionName, 1024);
  }
  if (continueFlag)
  {
    return True;
  }
  return False;
}

static
Bool useFiltering(void)
{
  if (suppressSubcalls)
  {
    if (getFunctionName(curIAddr, False, False))
    {
      return (VG_(HT_lookup) (funcNames, hashCode(diFunctionName)) != NULL || checkWildcards(diFunctionName));
    }
    return False;
  }
#define STACK_LOOKUP_DEPTH 30
  Addr ips[STACK_LOOKUP_DEPTH];
  Addr sps[STACK_LOOKUP_DEPTH];
  Addr fps[STACK_LOOKUP_DEPTH];
  Int found = VG_(get_StackTrace) (VG_(get_running_tid) (), ips, STACK_LOOKUP_DEPTH, sps, fps, 0);
#undef STACK_LOOKUP_DEPTH
  Int i;
  for (i = 0; i < found; i ++)
  {
    if (getFunctionName(ips[i], False, False))
    {
      if (VG_(HT_lookup) (funcNames, hashCode(diFunctionName)) != NULL || checkWildcards(diFunctionName))
      {
        return True;
      }
    }
  }
  return False;
}

static
Bool dumpCall(void)
{
  if (getFunctionName(curIAddr, False, False))
  {
    if (cutAffixes(diFunctionName))
    {
      Char tmp[1024];
      VG_(strcpy) (tmp, diFunctionName);
      cutTemplates(tmp);
      if (VG_(HT_lookup) (funcNames, hashCode(tmp)) == NULL)
      {
        Char b[1024];
        Char obj[1024];
        Bool isStandard = False;
        if (VG_(get_objname) ((Addr)(curIAddr), obj, 1024))
        {
          isStandard = isStandardFunction(obj);
        }
        if (!isStandard)
        {
          Int l;
          l = VG_(sprintf) (b, "%s\n", diFunctionName);
          my_write(fdfuncFilter, b, l);
          fnNode* node;
          node = VG_(malloc)("fnNode", sizeof(fnNode));
          node->key = hashCode(tmp);
          node->data = NULL;
          VG_(HT_add_node) (funcNames, node);
        }
      }
    }
    return True;
  }
  return False;
}

static
Char* concatTempDir(Char* fileName)
{
  Char* result;
  if (tempDir == NULL)
  {
    result = VG_(malloc)(fileName, VG_(strlen)(fileName) + 1);
    VG_(strcpy)(result, fileName);
  }
  else
  {
    Int length = VG_(strlen)(tempDir);
    result = VG_(malloc)(fileName, length + VG_(strlen)(fileName) + 1);
    VG_(strcpy)(result, tempDir);
    VG_(strcpy)(result + length, fileName);
    result[length + VG_(strlen)(fileName)] = '\0';
  }
  return result;
}

static
HWord getDecimalValue(IRExpr* e, HWord value)
{
  if (e->tag == Iex_Const)
  {
    IRConst* con = e->Iex.Const.con;
    switch (con->tag)
    {
      case Ico_U1:	return con->Ico.U1;
      case Ico_U8:	return con->Ico.U8;
      case Ico_U16:	return con->Ico.U16;
      case Ico_U32:	return con->Ico.U32;
      case Ico_U64:	return con->Ico.U64;
      default:		return value;
    }
  }
  else
  {
    return value;
  }
}

static
void translateLongToPowerOfTwo(IRExpr* e, ULong value)
{
  ULong a = 0x1;
  ULong i = 1;
  Char s[256];
  for (; i < value; i++)
  {
    a <<= 1;
  }
  Int l = VG_(sprintf)(s, "0hex%016llx", a);
  my_write(fdtrace, s, l);
  my_write(fddanger, s, l);
}

static
void translateToPowerOfTwo(IRExpr* e, HWord value, UShort size)
{
  ULong a = 0x1;
  ULong i = 1;
  HWord v = getDecimalValue(e, value);
  Char s[256];
  Int l = 0;
  for (; i < v; i++)
  {
    a <<= 1;
  }
  if ((e->tag != Iex_Const) && (size == 128))
  {
    l = VG_(sprintf)(s, "0hex%032llx", a);
  }
  else
  {
    switch (size)
    {
      case 1:		l = VG_(sprintf)(s, "0hex%lx", (HWord) a);
			break;
      case 8:		l = VG_(sprintf)(s, "0hex%02llx", a);
			break;
      case 16:		l = VG_(sprintf)(s, "0hex%04llx", a);
			break;
      case 32:		l = VG_(sprintf)(s, "0hex%08llx", a);
			break;
      case 64:		l = VG_(sprintf)(s, "0hex%016llx", a);
			break;
      default:		break;
    }
  }
  my_write(fdtrace, s, l);
  my_write(fddanger, s, l);
}

static
void translateLongValue(IRExpr* e, ULong value)
{
  Char s[256];
  Int l = VG_(sprintf)(s, "0hex%016llx", value);
  my_write(fdtrace, s, l);
  my_write(fddanger, s, l);
}

static
void translateValue(IRExpr* e, HWord value)
{
  Char s[256];
  Int l = 0;
  if (e->tag == Iex_Const)
  {
    IRConst* con = e->Iex.Const.con;
    switch (con->tag)
    {
      case Ico_U1:	l = VG_(sprintf)(s, "0hex%x", con->Ico.U1);
			break;
      case Ico_U8:	l = VG_(sprintf)(s, "0hex%02x", con->Ico.U8);
			break;
      case Ico_U16:	l = VG_(sprintf)(s, "0hex%04x", con->Ico.U16);
			break;
      case Ico_U32:	l = VG_(sprintf)(s, "0hex%08x", con->Ico.U32);
			break;
      case Ico_U64:	l = VG_(sprintf)(s, "0hex%016llx", con->Ico.U64);
			break;
      default:		break;
    }
  }
  else
  {
    switch (curNode->tempSize[e->Iex.RdTmp.tmp])
    {
      case 1:	l = VG_(sprintf)(s, "0bin%lx", value);
                break;
      case 8:	l = VG_(sprintf)(s, "0hex%02lx", value);
                break;
      case 16:	l = VG_(sprintf)(s, "0hex%04lx", value);
                break;
      case 32:	l = VG_(sprintf)(s, "0hex%08lx", value);
                break;
      case 64:	l = VG_(sprintf)(s, "0hex%016lx", value);
                break;
      case 128:	l = VG_(sprintf)(s, "0hex%032lx", value);
                break;
      default: 	break;
    }
  }
  my_write(fdtrace, s, l);
  my_write(fddanger, s, l);
}

static
void translateIRTmp(IRExpr* e)
{
  Char s[256];
  Int l = VG_(sprintf)(s, "t_%lx_%u_%u", curblock, e->Iex.RdTmp.tmp, curvisited);
  my_write(fdtrace, s, l);
  my_write(fddanger, s, l);
}

static
void instrumentIMark(HWord addr)
{
  curIAddr = addr;
#ifdef CALL_STACK_PRINTOUT
  printName = getFunctionName(addr, True, False);
  if (printName)
  {
    VG_(printf) ("%s\n", diFunctionName);
  }
#endif
#ifdef TAINTED_TRACE_PRINTOUT
  //VG_(printf)("------ IMark(0x%lx) ------\n", addr);
#endif
}

static
void taintMemoryFromArgv(HWord key, HWord offset)
{
  Char ss[256], argvFileBuf[256];
  Char *hyphenPos;
  Int l;
#define TEMP_SEGMENT_SIZE 6
  Char tempSegment[TEMP_SEGMENT_SIZE + 1];
  taintedNode* node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  node->key = key;
  node->filename = "argv_dot_log";
  node->offset = offset;
  node->fileIndex = 'a';
  VG_(HT_add_node)(taintedMemory, node);
  if (hostTempDir != NULL)
  {
    hyphenPos = VG_(strchr)(hostTempDir, '-');
  }
  else
  {
    hyphenPos = VG_(strchr)(tempDir, '-');
  }
  VG_(strncpy)(tempSegment, hyphenPos + 1, TEMP_SEGMENT_SIZE);
  tempSegment[TEMP_SEGMENT_SIZE] = '\0';
  VG_(sprintf)(argvFileBuf, "file__slash_tmp_slash_avalanche_hyphen_%s_slash_argv_dot_log", tempSegment);
  l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := %s[0hex%08lx];\n",
                   memory + 1, memory, key, argvFileBuf, offset);
  memory++;
  my_write(fdtrace, ss, l);
  my_write(fddanger, ss, l);
}

static
void taintMemoryFromFile(HWord key, HWord offset, Char fileIndex)
{
  Int l;
  Char ss[256];
  taintedNode* node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  node->key = key;
  node->filename = curfile;
  node->offset = offset;
  node->fileIndex = fileIndex;
  VG_(HT_add_node)(taintedMemory, node);
  l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := file_%s[0hex%08lx];\n", 
                   memory + 1, memory, key, curfile, offset);
  memory++;
  my_write(fdtrace, ss, l);
  my_write(fddanger, ss, l);
}

static
void taintMemoryFromSocket(HWord key, HWord offset)
{
  Int l;
  Char ss[256];
  taintedNode* node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  node->key = key;
  node->filename = NULL;
  node->fileIndex = 0;
  node->offset = offset;
  VG_(HT_add_node)(taintedMemory, node);
  l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := socket_%d[0hex%08lx];\n", 
                   memory + 1, memory, key, cursocket, offset);
  memory++;
  my_write(fdtrace, ss, l);
  my_write(fddanger, ss, l);
}

static
void taintMemory(HWord key, UShort size)
{
  taintedNode* node;
  switch (size)
  {
    case 8:	if (VG_(HT_lookup)(taintedMemory, key) == NULL)
                {
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
                }
		return;
    case 16:	if (VG_(HT_lookup)(taintedMemory, key) == NULL)
                {
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
                }
		if (VG_(HT_lookup)(taintedMemory, key + 1) == NULL)
		{
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key + 1;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
		}
		return;
    case 32:	if (VG_(HT_lookup)(taintedMemory, key) == NULL)
		{
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
		}
		if (VG_(HT_lookup)(taintedMemory, key + 1) == NULL)
		{
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key + 1;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
		}
		if (VG_(HT_lookup)(taintedMemory, key + 2) == NULL)
		{
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key + 2;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
		}
		if (VG_(HT_lookup)(taintedMemory, key + 3) == NULL)
		{
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key + 3;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
		}
                return;
    case 64:	if (VG_(HT_lookup)(taintedMemory, key) == NULL)
		{
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
		}
		if (VG_(HT_lookup)(taintedMemory, key + 1) == NULL)
		{
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key + 1;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
		}
		if (VG_(HT_lookup)(taintedMemory, key + 2) == NULL)
		{
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key + 2;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
		}
		if (VG_(HT_lookup)(taintedMemory, key + 3) == NULL)
		{
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key + 3;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
		}
		if (VG_(HT_lookup)(taintedMemory, key + 4) == NULL)
		{
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key + 4;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
		}
		if (VG_(HT_lookup)(taintedMemory, key + 5) == NULL)
		{
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key + 5;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
		}
		if (VG_(HT_lookup)(taintedMemory, key + 6) == NULL)
		{
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key + 6;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
		}
		if (VG_(HT_lookup)(taintedMemory, key + 7) == NULL)
		{
		  node = VG_(malloc)("taintMemoryNode", sizeof(taintedNode));
  		  node->key = key + 7;
		  node->filename = NULL;
		  VG_(HT_add_node)(taintedMemory, node);
		}
		return;
  }
}

static
void untaintMemory(HWord key, UShort size)
{
  taintedNode* node;
  switch (size)
  {
    case 8:	node = VG_(HT_remove)(taintedMemory, key);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		return;
    case 16:	node = VG_(HT_remove)(taintedMemory, key);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedMemory, key + 1);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		return;
    case 32:	node = VG_(HT_remove)(taintedMemory, key);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedMemory, key + 1);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedMemory, key + 2);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedMemory, key + 3);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
                return;
    case 64:	node = VG_(HT_remove)(taintedMemory, key);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedMemory, key + 1);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedMemory, key + 2);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedMemory, key + 3);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedMemory, key + 4);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedMemory, key + 5);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedMemory, key + 6);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedMemory, key + 7);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		return;
  }
}

static
void taintRegister(HWord key, UShort size)
{
  taintedNode* node;
  switch (size)
  {
    case 8:	if (VG_(HT_lookup)(taintedRegisters, key) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
                return;
    case 16:	if (VG_(HT_lookup)(taintedRegisters, key) == NULL)
		{
		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		if (VG_(HT_lookup)(taintedRegisters, key + 1) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key + 1;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		return;
    case 32:	if (VG_(HT_lookup)(taintedRegisters, key) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		if (VG_(HT_lookup)(taintedRegisters, key + 1) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key + 1;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		if (VG_(HT_lookup)(taintedRegisters, key + 2) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key + 2;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		if (VG_(HT_lookup)(taintedRegisters, key + 3) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key + 3;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		return;
    case 64:	if (VG_(HT_lookup)(taintedRegisters, key) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		if (VG_(HT_lookup)(taintedRegisters, key + 1) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key + 1;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		if (VG_(HT_lookup)(taintedRegisters, key + 2) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key + 2;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		if (VG_(HT_lookup)(taintedRegisters, key + 3) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key + 3;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		if (VG_(HT_lookup)(taintedRegisters, key + 4) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key + 4;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		if (VG_(HT_lookup)(taintedRegisters, key + 5) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key + 5;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		if (VG_(HT_lookup)(taintedRegisters, key + 6) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key + 6;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		if (VG_(HT_lookup)(taintedRegisters, key + 7) == NULL)
		{
  		  node = VG_(malloc)("taintRegisterNode", sizeof(taintedNode));
  		  node->key = key + 7;
  		  VG_(HT_add_node)(taintedRegisters, node);
		}
		return;
  }
}

static
void untaintRegister(HWord key, UShort size)
{
  taintedNode* node;
  switch (size)
  {
    case 8:	node = VG_(HT_remove)(taintedRegisters, key);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		return;
    case 16:	node = VG_(HT_remove)(taintedRegisters, key);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedRegisters, key + 1);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		return;
    case 32:	node = VG_(HT_remove)(taintedRegisters, key);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedRegisters, key + 1);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedRegisters, key + 2);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedRegisters, key + 3);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
                return;
    case 64:	node = VG_(HT_remove)(taintedRegisters, key);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedRegisters, key + 1);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedRegisters, key + 2);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedRegisters, key + 3);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedRegisters, key + 4);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedRegisters, key + 5);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedRegisters, key + 6);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		node = VG_(HT_remove)(taintedRegisters, key + 7);
		if (node != NULL)
		{
		  VG_(free)(node);
		}
		return;
  }
}

static
void taintTemp(HWord key)
{
  taintedNode* node = VG_(malloc)("taintTempNode", sizeof(taintedNode));
  node->key = key;
  VG_(HT_add_node)(taintedTemps, node);
  Char s[256];
  Int l = VG_(sprintf)(s, "t_%lx_%lu_%u : BITVECTOR(%u);\n", curblock, key, curvisited, curNode->tempSize[key]);
  my_write(fdtrace, s, l);
  my_write(fddanger, s, l);
}

static
void pre_call(ThreadId tid, UInt syscallno)
{
  if (syscallno == __NR_read)
  {
    isRead = True;
  }
  else if (syscallno == __NR_open)
  {
    isOpen = True;
  }
}

static
void post_call(ThreadId tid, UInt syscallno, SysRes res)
{
  //VG_(printf) ("post_call, syscallno = %u\n", syscallno);
  if (syscallno == __NR_read)
  {
    isRead = False;
  }
  else if ((syscallno == __NR_clone) && !sr_isError(res) && (sr_Res(res) == 0))
  {
    VG_(printf)("__NR_clone\n");
    //VG_(exit)(0);
  }
  else if (syscallno == __NR_open)
  {
    isOpen = False;
    if ((curfile != NULL) && !curDeclared)
    {
      Char s[256];
      Int l = VG_(sprintf)(s, "file_%s : ARRAY BITVECTOR(32) OF BITVECTOR(8);\n", curfile);
      my_write(fdtrace, s, l);
      my_write(fddanger, s, l);
    }
  }
  else if (addTaintedSocket && (cursocket != -1))
  {
    Char s[256];
    Int l = VG_(sprintf)(s, "socket_%d : ARRAY BITVECTOR(32) OF BITVECTOR(8);\n", cursocket);
    my_write(fdtrace, s, l);
    my_write(fddanger, s, l);
    addTaintedSocket = False;
  }
}

static
void tg_track_post_mem_write(CorePart part, ThreadId tid, Addr a, SizeT size)
{
  UWord index;
  if (isRead && (curfile != NULL))
  {
    Int i;
    Bool makeNewEntry = True;
    for (i = 0; i < VG_(sizeXA) (inputFiles); i ++)
    {
      if (!VG_(strcmp) (*((Char**)(VG_(indexXA) (inputFiles, i))), curfile))
      {
        makeNewEntry = False;
        break;
      }
    }
    if (makeNewEntry)
    {
      Char *newInputFile = VG_(strdup) ("inputFilesEntry", curfile);
      VG_(addToXA) (inputFiles, &newInputFile);
    }
    for (index = a; (index < (a + size)) && (curoffs + (index - a) < cursize); index += 1)
    {
      if (inputFilterEnabled)
      {
        if (checkInputOffset(curfilenum, curoffs + (index - a)))
        {
          taintMemoryFromFile(index, curoffs + (index - a), i + 1);
        }
      }
      else taintMemoryFromFile(index, curoffs + (index - a), i + 1);

    }
  }
  else if ((isRead || isRecv) && (sockets || datagrams) && (cursocket != -1))
  {
    if (replace)
    {
      if (cursocket >= socketsNum)
      {
        if (replace_data == NULL)
        {
          replace_data = (replaceData*) VG_(malloc)("replace_data", (cursocket + 1) * sizeof(replaceData));
        }
        else
        {
          replace_data = (replaceData*) VG_(realloc)("replace_data", replace_data, (cursocket + 1) * sizeof(replaceData));
        }
        Int i = socketsNum;
        for (; i <= cursocket; i++)
        {
          replace_data[i].length = 0;
          replace_data[i].data = NULL;
        }
        socketsNum = cursocket + 1;
      }
      Int oldlength = replace_data[cursocket].length;
      if (replace_data[cursocket].length < curoffs + size)
      {
        replace_data[cursocket].data = (UChar*) VG_(realloc)("replace_data", replace_data[cursocket].data, curoffs + size);
        VG_(memset)(replace_data[cursocket].data + replace_data[cursocket].length, 0, curoffs + size - replace_data[cursocket].length);
        replace_data[cursocket].length = curoffs + size;
      }
      for (index = a; index < a + size; index++)
      {
        if ((cursocket < socketsBoundary) && (curoffs + (index - a) < oldlength))
        {
          *((UChar*) index) = replace_data[cursocket].data[curoffs + (index - a)];
        }
        else
        {
          replace_data[cursocket].data[curoffs + (index - a)] = *((UChar*) index);
        }
        if (checkInputOffset(cursocket, curoffs + (index - a)))
        {
          taintMemoryFromSocket(index, curoffs + (index - a));
        }
      }
    }
    else
    {
      for (index = a; index < a + size; index++)
      {
        if (checkInputOffset(cursocket, curoffs + (index - a)))
        {
          taintMemoryFromSocket(index, curoffs + (index - a));
        }
      }
    }
  }
}

static
void tg_track_mem_mmap(Addr a, SizeT size, Bool rr, Bool ww, Bool xx, ULong di_handle)
{
  Addr index = a;
  if (isMap && (curfile != NULL))
  {
    Int i;
    Bool makeNewEntry = True;
    for (i = 0; i < VG_(sizeXA) (inputFiles); i ++)
    {
      if (!VG_(strcmp) (VG_(indexXA) (inputFiles, i), curfile))
      {
        makeNewEntry = False;
        break;
      }
    }
    if (makeNewEntry)
    {
      Char* newInputFile = VG_(strdup)("inputFilesEntry", curfile);
      VG_(addToXA) (inputFiles, &newInputFile);
    }
    for (index = a; (index < (a + size)) && (index < (a + cursize)); index += 1)
    {
      if (inputFilterEnabled)
      {
        if (checkInputOffset(curfilenum, index - a))
        {
          taintMemoryFromFile(index, index - a, i + 1);
        }
      }
      else taintMemoryFromFile(index, index - a, i + 1);
    }
  }
  isMap = False;
}

static
void instrumentPutLoad(IRStmt* clone, UInt offset, IRExpr* loadAddr)
{
  UShort size;
  switch (clone->Ist.Put.data->Iex.Load.ty)
  {
    case Ity_I8:	size = 8;
			break;
    case Ity_I16:	size = 16;
			break;
    case Ity_I32:	size = 32;
			break;
    case Ity_I64:	size = 64;
			break;
    default:        return;
  }
  if (VG_(HT_lookup)(taintedMemory, (UWord) loadAddr) != NULL)
  {
    taintRegister(offset, size);
#ifdef TAINTED_TRACE_PRINTOUT
    ppIRStmt(clone);
    VG_(printf) ("\n");
#endif
    Char ss[256];
    Int l = 0;
    UWord addr = (UWord) loadAddr;
    switch (size)
    {
      case 8:	l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 1, registers, offset, memory, addr);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                registers++;
                break;
      case 16:	l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 1, registers, offset, memory, addr);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 2, registers + 1, offset + 1, memory, addr + 1);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                registers += 2;
                break;
      case 32:  l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 1, registers, offset, memory, addr);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 2, registers + 1, offset + 1, memory, addr + 1);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 3, registers + 2, offset + 2, memory, addr + 2);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 4, registers + 3, offset + 3, memory, addr + 3);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                registers += 4;
                break;
      case 64:  l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 1, registers, offset, memory, addr);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 2, registers + 1, offset + 1, memory, addr + 1);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 3, registers + 2, offset + 2, memory, addr + 2);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 4, registers + 3, offset + 3, memory, addr + 3);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 5, registers + 4, offset + 4, memory, addr + 4);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 6, registers + 5, offset + 5, memory, addr + 5);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 7, registers + 6, offset + 6, memory, addr + 6);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := memory_%d[0hex" PTR_FMT "];\n", registers + 8, registers + 7, offset + 7, memory, addr + 7);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                registers += 8;
                break;
      default:	break;
    }
  }
  else
  {
    untaintRegister(offset, size);
  }
}

static
void instrumentPutGet(IRStmt* clone, UInt putOffset, UInt getOffset)
{
  UShort size;
  switch (clone->Ist.Put.data->Iex.Get.ty)
  {
    case Ity_I8:	size = 8;
			break;
    case Ity_I16:	size = 16;
			break;
    case Ity_I32:	size = 32;
			break;
    case Ity_I64:	size = 64;
			break;
    default:        return;
  }
  if (VG_(HT_lookup)(taintedRegisters, getOffset) != NULL)
  {
    taintRegister(putOffset, size);
#ifdef TAINTED_TRACE_PRINTOUT
    ppIRStmt(clone);
    VG_(printf) ("\n");
#endif
    Char ss[256];
    Int l = 0;
    switch (size)
    {
      case 8:	l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 1, registers, putOffset, registers, getOffset);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                registers++;
                break;
      case 16:	l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 1, registers, putOffset, registers, getOffset);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 2, registers + 1, putOffset + 1, registers + 1, getOffset + 1);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                registers += 2;
                break;
      case 32:  l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 1, registers, putOffset, registers, getOffset);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 2, registers + 1, putOffset + 1, registers + 1, getOffset + 1);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 3, registers + 2, putOffset + 2, registers + 2, getOffset + 2);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 4, registers + 3, putOffset + 3, registers + 3, getOffset + 3);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                registers += 4;
                break;
      case 64:  l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 1, registers, putOffset, registers, getOffset);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 2, registers + 1, putOffset + 1, registers + 1, getOffset + 1);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 3, registers + 2, putOffset + 2, registers + 2, getOffset + 2);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 4, registers + 3, putOffset + 3, registers + 3, getOffset + 3);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 5, registers + 4, putOffset + 4, registers + 4, getOffset + 4);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 6, registers + 5, putOffset + 5, registers + 5, getOffset + 5);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 7, registers + 6, putOffset + 6, registers + 6, getOffset + 6);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := registers_%d[0hex%02x];\n", registers + 8, registers + 7, putOffset + 7, registers + 7, getOffset + 7);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                registers += 8;
                break;
      default:	break;
    }
  }
  else
  {
    untaintRegister(putOffset, size);
  }
}

static
void instrumentPutRdTmp(IRStmt* clone, UInt offset, UInt tmp)
{
  if (VG_(HT_lookup)(taintedTemps, tmp) != NULL)
  {
    taintRegister(offset, curNode->tempSize[tmp]);
#ifdef TAINTED_TRACE_PRINTOUT
    ppIRStmt(clone);
    VG_(printf) ("\n");
#endif
    Char ss[256];
    Int l = 0;
    switch (curNode->tempSize[tmp])
    {
      case 8:	l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u;\n", registers + 1, registers, offset, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                registers++;
                break;
      case 16:	l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[7:0];\n", registers + 1, registers, offset, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[15:8];\n", registers + 2, registers + 1, offset + 1, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                registers += 2;
                break;
      case 32:  l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[7:0];\n", registers + 1, registers, offset, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[15:8];\n", registers + 2, registers + 1, offset + 1, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[23:16];\n", registers + 3, registers + 2, offset + 2, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[31:24];\n", registers + 4, registers + 3, offset + 3, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                registers += 4;
                break;
      case 64:  l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[7:0];\n", registers + 1, registers, offset, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[15:8];\n", registers + 2, registers + 1, offset + 1, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[23:16];\n", registers + 3, registers + 2, offset + 2, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[31:24];\n", registers + 4, registers + 3, offset + 3, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
		l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[39:32];\n", registers + 5, registers + 4, offset + 4, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[47:40];\n", registers + 6, registers + 5, offset + 5, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[55:48];\n", registers + 7, registers + 6, offset + 6, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "registers_%d : ARRAY BITVECTOR(8) OF BITVECTOR(8) = registers_%d WITH [0hex%02x] := t_%lx_%u_%u[63:56];\n", registers + 8, registers + 7, offset + 7, curblock, tmp, curvisited);
  		my_write(fdtrace, ss, l);
  		my_write(fddanger, ss, l);
                registers += 8;
                break;
      default:	break;
    }
  }
  else
  {
    untaintRegister(offset, curNode->tempSize[tmp]);
  }
}

static
void instrumentPutConst(IRStmt* clone, UInt offset)
{
  switch (clone->Ist.Put.data->Iex.Const.con->tag)
  {
    case Ico_U8:	untaintRegister(offset, 8);
			break;
    case Ico_U16:	untaintRegister(offset, 16);
			break;
    case Ico_U32:	untaintRegister(offset, 32);
 			break;
    case Ico_U64:	untaintRegister(offset, 64);
 			break;
    default:		break;
  }
}

static
void instrumentWrTmpLoad(IRStmt* clone, IRExpr* loadAddr)
{
  UInt tmp = clone->Ist.WrTmp.tmp;
  UInt rtmp = clone->Ist.WrTmp.data->Iex.Load.addr->Iex.RdTmp.tmp;
  HWord addr = (HWord) loadAddr;

  /* This shouldn't work properly without VG_(am_get_client_segment_starts),
     better remove it. Also address is not guaranteed to be in a temporary
     anymore, it can be a number - (check issue 7 on googlecode). */

  /* if (checkDanger && (VG_(HT_lookup)(taintedTemps, rtmp) != NULL) && (!enableFiltering || useFiltering()))
  {
    Char s[256];
    Int l = 0;
    Addr addrs[256];
    //Int segs = VG_(am_get_client_segment_starts)(addrs, 256);
    const NSegment* seg = VG_(am_find_nsegment)(addrs[0]);
    Char format[256];

    VG_(sprintf)(format, "ASSERT(BVLT(t_%%lx_%%u_%%u, 0hex%%0%ux));\nQUERY(FALSE);\n",
                 curNode->tempSize[rtmp] / 4);
    if (fdfuncFilter >= 0)
    {
      dumpCall();
    }
    l = VG_(sprintf)(s, format, curblock, rtmp, curvisited, seg->start);
    my_write(fddanger, s, l);
  } */

  taintedNode* t = VG_(HT_lookup)(taintedMemory, addr);
  if (t != NULL)
  {
    Char s[1024];
    Int l = 0;

    taintTemp(tmp);
#ifdef TAINTED_TRACE_PRINTOUT
    ppIRStmt(clone);
    VG_(printf) ("\n");
#endif
    switch (curNode->tempSize[tmp])
    {
      case 8:   l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=memory_%d[0hex" PTR_FMT "]);\n",
                                    curblock, tmp, curvisited, memory, addr);
                break;
      case 16:  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=((memory_%d[0hex" PTR_FMT "] @ 0hex00) | "
                                                        "(0hex00 @ memory_%d[0hex" PTR_FMT "])));\n",
                                    curblock, tmp, curvisited, memory, addr + 1, memory, addr);
                break;
      case 32:  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=((memory_%d[0hex" PTR_FMT "] @ 0hex000000) | "
                                                        "(0hex00 @ memory_%d[0hex" PTR_FMT "] @ 0hex0000) | "
                                                        "(0hex0000 @ memory_%d[0hex" PTR_FMT "] @ 0hex00) | "
                                                        "(0hex000000 @ memory_%d[0hex" PTR_FMT "])));\n", 
                                    curblock, tmp, curvisited, memory, addr + 3, memory, addr + 2, memory, addr + 1, memory, addr);
                break;
      case 64:  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=((memory_%d[0hex" PTR_FMT "] @ 0hex00000000000000) | "
                                                        "(0hex00 @ memory_%d[0hex" PTR_FMT "] @ 0hex000000000000) | "
                                                        "(0hex0000 @ memory_%d[0hex" PTR_FMT "] @ 0hex0000000000) | "
                                                        "(0hex000000 @ memory_%d[0hex" PTR_FMT "] @ 0hex00000000) | "
                                                        "(0hex00000000 @ memory_%d[0hex" PTR_FMT "] @ 0hex000000) | "
                                                        "(0hex0000000000 @ memory_%d[0hex" PTR_FMT "] @ 0hex0000) | "
                                                        "(0hex000000000000 @ memory_%d[0hex" PTR_FMT "] @ 0hex00) | "
                                                        "(0hex00000000000000 @ memory_%d[0hex" PTR_FMT "])));\n",
                                    curblock, tmp, curvisited, memory, addr + 7, memory, addr + 6, memory, addr + 5, 
                                                               memory, addr + 4, memory, addr + 3, memory, addr + 2, 
                                                               memory, addr + 1, memory, addr);
                break;
      default:  break;
    }
    my_write(fdtrace, s, l);
    my_write(fddanger, s, l);
    /* The first instruction in the chain of tainted operations is always
         load from memory to IRTmp. Those tainted nodes that have filename
         correspond to data directly read from input files. Only offsets
         that are encountered here are used in the current run.
       
       Nodes with fileIndex = 'a' corresponds to program arguments.
         We don't want these to be included in offsets.log. */
    Int size = curNode->tempSize[tmp];
    if ((t->fileIndex != '\0') && 
        (t->fileIndex != 'a') 
        && (t->filename != NULL))
    {
      Int i = 0;
      OSet *offsetSet;
      /* Haven't previously encountered loads from this file. Add it! */
      if (t->fileIndex - 1 >= VG_(sizeXA) (usedOffsets))
      {
        offsetSet = VG_(OSetWord_Create) (VG_(malloc), 
                                          "usedOffsetsChunk", VG_(free));
        VG_(addToXA) (usedOffsets, &offsetSet);
      }
      else
      {
        offsetSet = *((OSet **)VG_(indexXA) (usedOffsets, t->fileIndex - 1));
      }
      /* We have to get initial offsets of all loaded bytes, 
           so we load all nodes.*/
      do
      {
        if (!VG_(OSetWord_Contains) (offsetSet, t->offset))
	{ 
	  VG_(OSetWord_Insert) (offsetSet, t->offset);
	}
        i ++;
	t = VG_(HT_lookup) (taintedMemory, addr + i);
      }
      while ((i < (size >> 3)) && (t != NULL));
    }
  }
}

static
void instrumentWrTmpGet(IRStmt* clone, UInt tmp, UInt offset)
{
  if (VG_(HT_lookup)(taintedRegisters, offset) != NULL)
  {
    Char s[1024];
    Int l = 0;
    taintTemp(tmp);
    switch (curNode->tempSize[tmp])
    {
      case 8:   l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=registers_%d[0hex%02x]);\n", 
                                    curblock, tmp, curvisited, registers, offset);
                break;
      case 16:  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=((0hex00 @ registers_%d[0hex%02x]) | "
                                                        "(registers_%d[0hex%02x] @ 0hex00)));\n", 
                                    curblock, tmp, curvisited, registers, offset, registers, offset + 1);
                break;
      case 32:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=((0hex000000 @ registers_%d[0hex%02x]) | "
                                                        "(0hex0000 @ registers_%d[0hex%02x] @ 0hex00) | "
                                                        "(0hex00 @ registers_%d[0hex%02x] @ 0hex0000) | "
                                                        "(registers_%d[0hex%02x] @ 0hex000000)));\n", 
                                    curblock, tmp, curvisited, registers, offset, registers, offset + 1, 
                                                               registers, offset + 2, registers, offset + 3);
                break;
      case 64:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=((0hex00000000000000 @ registers_%d[0hex%02x]) | "
                                                        "(0hex000000000000 @ registers_%d[0hex%02x] @ 0hex00) | "
                                                        "(0hex0000000000 @ registers_%d[0hex%02x] @ 0hex0000) | "
                                                        "(0hex00000000 @ registers_%d[0hex%02x] @ 0hex000000) | "
                                                        "(0hex000000 @ registers_%d[0hex%02x] @ 0hex00000000) | "
                                                        "(0hex0000 @ registers_%d[0hex%02x] @ 0hex0000000000) | "
                                                        "(0hex00 @ registers_%d[0hex%02x] @ 0hex000000000000) | "
                                                        "(registers_%d[0hex%02x] @ 0hex00000000000000)));\n", 
                                    curblock, tmp, curvisited, registers, offset, registers, offset + 1, 
                                                               registers, offset + 2, registers, offset + 3, 
                                                               registers, offset + 4, registers, offset + 5, 
                                                               registers, offset + 6, registers, offset + 7);
                break;
      default:  break;
    }
    my_write(fdtrace, s, l);
    my_write(fddanger, s, l);
#ifdef TAINTED_TRACE_PRINTOUT
    ppIRStmt(clone);
    VG_(printf) ("\n");
#endif
  }
}

static
void instrumentWrTmpRdTmp(IRStmt* clone, UInt ltmp, UInt rtmp)
{
  if (VG_(HT_lookup)(taintedTemps, rtmp) != NULL)
  {
    Char s[256];
    taintTemp(ltmp);
#ifdef TAINTED_TRACE_PRINTOUT
    ppIRStmt(clone);
    VG_(printf) ("\n");
#endif
    Int l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=t_%lx_%u_%u);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
    my_write(fdtrace, s, l);
    my_write(fddanger, s, l);
  }
}

static
void instrumentWrTmpUnop(IRStmt* clone, UInt ltmp, UInt rtmp, IROp op)
{
  if (VG_(HT_lookup)(taintedTemps, rtmp) != NULL)
  {
    taintTemp(ltmp);
#ifdef TAINTED_TRACE_PRINTOUT
    ppIRStmt(clone);
    VG_(printf) ("\n");
#endif
    Char s[256];
    Int l = 0;
    switch (op)
    {
      case Iop_1Uto8:   	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=0bin0000000@t_%lx_%u_%u);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_1Uto32:  	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=0bin0000000000000000000000000000000@t_%lx_%u_%u);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_1Uto64:  	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=0bin000000000000000000000000000000000000000000000000000000000000000@t_%lx_%u_%u);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_8Uto16:  	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=0hex00@t_%lx_%u_%u);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_8Uto32:  	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=0hex000000@t_%lx_%u_%u);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_8Uto64:  	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=0hex00000000000000@t_%lx_%u_%u);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_16Uto32: 	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=0hex0000@t_%lx_%u_%u);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_16Uto64: 	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=0hex000000000000@t_%lx_%u_%u);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_32Uto64: 	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=0hex00000000@t_%lx_%u_%u);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_1Sto8:
      case Iop_1Sto16:
      case Iop_1Sto32:
      case Iop_1Sto64:
      case Iop_8Sto16:
      case Iop_8Sto32:
      case Iop_8Sto64:  	
      case Iop_16Sto32:
      case Iop_16Sto64:
      case Iop_32Sto64:     l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=BVSX(t_%lx_%u_%u, %d));\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited, curNode->tempSize[ltmp]);
				break;
      case Iop_16to8:
      case Iop_32to8:
      case Iop_64to8:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=t_%lx_%u_%u[7:0]);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_32to16:
      case Iop_64to16:
				l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=t_%lx_%u_%u[15:0]);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_64to32:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=t_%lx_%u_%u[31:0]);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_32to1:
      case Iop_64to1:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=t_%lx_%u_%u[0:0]);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_16HIto8:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=t_%lx_%u_%u[15:8]);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_32HIto16:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=t_%lx_%u_%u[31:16]);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_64HIto32:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=t_%lx_%u_%u[63:32]);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;


      case Iop_Not1:
      case Iop_Not8:
      case Iop_Not16:
      case Iop_Not32:
      case Iop_Not64:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=~t_%lx_%u_%u);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      case Iop_ReinterpF32asI32:
      case Iop_ReinterpI32asF32:
      case Iop_ReinterpF64asI64:
      case Iop_ReinterpI64asF64:l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=t_%lx_%u_%u);\n", curblock, ltmp, curvisited, curblock, rtmp, curvisited);
				break;
      default:		break;
    }
    my_write(fdtrace, s, l);
    my_write(fddanger, s, l);
  }
}

UShort isPropagation2(IRExpr* arg1, IRExpr* arg2)
{
  UShort res = 0;
  if (arg1->tag == Iex_RdTmp)
  {
    res = (VG_(HT_lookup)(taintedTemps, arg1->Iex.RdTmp.tmp) != NULL) ? 1 : 0;
  }
  if (arg2->tag == Iex_RdTmp)
  {
    res |= (VG_(HT_lookup)(taintedTemps, arg2->Iex.RdTmp.tmp) != NULL) ? 0x2 : 0;
  }
  return res;
}

static
UShort isPropagation3(IRExpr* arg1, IRExpr* arg2, IRExpr* arg3)
{
  UShort res = 0;
  if (arg1->tag == Iex_RdTmp)
  {
    res = (VG_(HT_lookup)(taintedTemps, arg1->Iex.RdTmp.tmp) != NULL) ? 1 : 0;
  }
  if (arg2->tag == Iex_RdTmp)
  {
    res |= (VG_(HT_lookup)(taintedTemps, arg2->Iex.RdTmp.tmp) != NULL) ? 0x2 : 0;
  }
  if (arg3->tag == Iex_RdTmp)
  {
    res |= (VG_(HT_lookup)(taintedTemps, arg3->Iex.RdTmp.tmp) != NULL) ? 0x4 : 0;
  }
  return res;
}

Bool firstTainted(UShort res)
{
  return res & 0x1;
}

Bool secondTainted(UShort res)
{
  return res & 0x2;
}

static 
Bool thirdTainted(UShort res)
{
  return res & 0x4;
}

static
void translateLong1(IRExpr* arg, ULong value, UShort taintedness)
{
  if (firstTainted(taintedness))
  {
    translateIRTmp(arg);
  }
  else
  {
    translateLongValue(arg, value);
  }
}

static
void translateLong2(IRExpr* arg, ULong value, UShort taintedness)
{
  if (secondTainted(taintedness))
  {
    translateIRTmp(arg);
  }
  else
  {
    translateLongValue(arg, value);
  }
}

static
void translate1(IRExpr* arg, HWord value, UShort taintedness)
{
  if (firstTainted(taintedness))
  {
    translateIRTmp(arg);
  }
  else
  {
    translateValue(arg, value);
  }
}

static
void translate2(IRExpr* arg, HWord value, UShort taintedness)
{
  if (secondTainted(taintedness))
  {
    translateIRTmp(arg);
  }
  else
  {
    translateValue(arg, value);
  }
}

static
void translate3(IRExpr* arg, HWord value, UShort taintedness)
{
  if (thirdTainted(taintedness))
  {
    translateIRTmp(arg);
  }
  else
  {
    translateValue(arg, value);
  }
}

//TODO: Do this properly.
//      Don't want additional params in printSizedBool
static
void printSizedBool_DangerOnly(UShort size, Bool value)
{
  Char s[256];
  Int l = 0;
  Int v = (value) ? 1 : 0;
  switch (size)
  {
    case 1:  l = VG_(sprintf)(s, "0bin%d", v);                  break;
    case 8:  l = VG_(sprintf)(s, "0hex0%d", v);                 break;
    case 16: l = VG_(sprintf)(s, "0hex000%d", v);               break;
    case 32: l = VG_(sprintf)(s, "0hex0000000%d", v);           break;
    case 64: l = VG_(sprintf)(s, "0hex000000000000000%d", v);   break;
    default: return;
  }
  my_write(fddanger, s, l);
}

static
void printSizedBool(UShort size, Bool value)
{
  Char s[256];
  Int l = 0;
  Int v = (value) ? 1 : 0;
  switch (size)
  {
    case 1:	l = VG_(sprintf)(s, "0bin%d", v);
		break;
    case 8:	l = VG_(sprintf)(s, "0hex0%d", v);
		break;
    case 16:	l = VG_(sprintf)(s, "0hex000%d", v);
		break;
    case 32:	l = VG_(sprintf)(s, "0hex0000000%d", v);
		break;
    case 64:	l = VG_(sprintf)(s, "0hex000000000000000%d", v);
		break;
    default:    return;
  }
  my_write(fdtrace, s, l);
  my_write(fddanger, s, l);
}

static
void instrumentWrTmpMux0X(IRStmt* clone, HWord condValue, HWord value0, HWord valueX)
{
  IRExpr *cond, *arg0, *argX;
  cond = clone->Ist.WrTmp.data->Iex.Mux0X.cond;
  arg0 = clone->Ist.WrTmp.data->Iex.Mux0X.expr0;
  argX = clone->Ist.WrTmp.data->Iex.Mux0X.exprX;
  UShort r = isPropagation3(cond, arg0, argX);
  if (firstTainted(r) ||
      ( (cond == 0) && secondTainted(r) ) ||
      ( (cond != 0) && thirdTainted(r) ))
  {
#ifdef TAINTED_TRACE_PRINTOUT
    ppIRStmt(clone);
    VG_(printf) ("\n");
#endif
    UInt l, ltmp = clone->Ist.WrTmp.tmp;
    Char s[256];
    taintTemp(ltmp);
    l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF ", curblock, ltmp, curvisited);
    my_write(fdtrace, s, l);
    my_write(fddanger, s, l);
    translate1(cond, condValue, r);
    my_write(fdtrace, "=", 1);
    my_write(fddanger, "=", 1);
    printSizedBool(curNode->tempSize[cond->Iex.RdTmp.tmp], False);
    my_write(fdtrace, " THEN ", 6);
    my_write(fddanger, " THEN ", 6);
    translate2(arg0, value0, secondTainted(r));
    my_write(fdtrace, " ELSE ", 6);
    my_write(fddanger, " ELSE ", 6);
    translate3(argX, valueX, thirdTainted(r));
    my_write(fdtrace, " ENDIF);\n", 9);
    my_write(fddanger, " ENDIF);\n", 9);
  }
}

/*---------------------------------------------------------------------------*/
/*---------------------------instrumentWrTmpCCall----------------------------*/
/*---------------------------------------------------------------------------*/

/* All actual instrumentation of WrTmpCCall takes place in 
   instrumentWrTmpCCall_Internal which is common for {x86, amd64, ARM}. 

   instrumentWrTmpCCall_Internal is called by a dirty helper 
   instrumentWrTmpCCall which is unique for {x86, amd64, ARM}.

   Call to instrumentWrTmpCCall is inserted into SuperBlock by
   instrumentWrTmpLongCCall_External which is unique for {x86, amd64, ARM}. */


void instrumentWrTmpCCall_Internal(UInt op, UInt ltmp, 
                                   UShort taintedness, 
                                   const Char* bitVectorModifier,
                                   IRExpr* arg1, IRExpr* arg2,
                                   HWord value1, HWord value2)
{
  Char s[256];
  Int l = 0;
  UShort size = curNode->tempSize[ltmp];
  taintTemp(ltmp);
  switch (op)
  {
    case BVLT:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF BVLT(", 
                                    curblock, ltmp, curvisited);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate1(arg1, value1, taintedness);
		l = VG_(sprintf)(s, "%s,", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate2(arg2, value2, taintedness);
		l = VG_(sprintf)(s, "%s) THEN ", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		printSizedBool(size, True);
		l = VG_(sprintf)(s, " ELSE ");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		printSizedBool(size, False);
		l = VG_(sprintf)(s, " ENDIF);\n");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
	   	break;
    case BVGE:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF BVGE(", curblock, ltmp, curvisited);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate1(arg1, value1, taintedness);
		l = VG_(sprintf)(s, "%s,", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate2(arg2, value2, taintedness);
		l = VG_(sprintf)(s, "%s) THEN ", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, True);
      		l = VG_(sprintf)(s, " ELSE ");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, False);
      		l = VG_(sprintf)(s, " ENDIF);\n");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
                break;
    case IFT:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF ", curblock, ltmp, curvisited);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate1(arg1, value1, taintedness);
                l = VG_(sprintf)(s, "%s=", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		translate2(arg2, value2, taintedness);
		l = VG_(sprintf)(s, "%s THEN ", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		printSizedBool(size, True);
		l = VG_(sprintf)(s, " ELSE ");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		printSizedBool(size, False);
		l = VG_(sprintf)(s, " ENDIF);\n");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		break;
    case IFNOT:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF NOT(", curblock, ltmp, curvisited);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate1(arg1, value1, taintedness);
                l = VG_(sprintf)(s, "%s=", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		translate2(arg2, value2, taintedness);
		l = VG_(sprintf)(s, "%s) THEN ", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		printSizedBool(size, True);
		l = VG_(sprintf)(s, " ELSE ");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		printSizedBool(size, False);
		l = VG_(sprintf)(s, " ENDIF);\n");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		break;
    case BVLE:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF BVLE(", curblock, ltmp, curvisited);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate1(arg1, value1, taintedness);
		l = VG_(sprintf)(s, "%s,", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate2(arg2, value2, taintedness);
		l = VG_(sprintf)(s, "%s) THEN ", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, True);
      		l = VG_(sprintf)(s, " ELSE ");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, False);
      		l = VG_(sprintf)(s, " ENDIF);\n");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
                break;
    case BVGT:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF BVGT(", curblock, ltmp, curvisited);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate1(arg1, value1, taintedness);
		l = VG_(sprintf)(s, "%s,", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate2(arg2, value2, taintedness);
		l = VG_(sprintf)(s, "%s) THEN ", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, True);
      		l = VG_(sprintf)(s, " ELSE ");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, False);
      		l = VG_(sprintf)(s, " ENDIF);\n");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
                break;
    case SBVLT:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF SBVLT(", curblock, ltmp, curvisited);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate1(arg1, value1, taintedness);
		l = VG_(sprintf)(s, "%s,", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate2(arg2, value2, taintedness);
		l = VG_(sprintf)(s, "%s) THEN ", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, True);
      		l = VG_(sprintf)(s, " ELSE ");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, False);
      		l = VG_(sprintf)(s, " ENDIF);\n");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
                break;
    case SBVGE:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF SBVGE(", curblock, ltmp, curvisited);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate1(arg1, value1, taintedness);
		l = VG_(sprintf)(s, "%s,", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate2(arg2, value2, taintedness);
		l = VG_(sprintf)(s, "%s) THEN ", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, True);
      		l = VG_(sprintf)(s, " ELSE ");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, False);
      		l = VG_(sprintf)(s, " ENDIF);\n");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
                break;
    case SBVLE:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF SBVLE(", curblock, ltmp, curvisited);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate1(arg1, value1, taintedness);
		l = VG_(sprintf)(s, "%s,", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate2(arg2, value2, taintedness);
		l = VG_(sprintf)(s, "%s) THEN ", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, True);
      		l = VG_(sprintf)(s, " ELSE ");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, False);
      		l = VG_(sprintf)(s, " ENDIF);\n");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
                break;
    case SBVGT:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF SBVGT(", curblock, ltmp, curvisited);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate1(arg1, value1, taintedness);
		l = VG_(sprintf)(s, "%s,", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
		translate2(arg2, value2, taintedness);
		l = VG_(sprintf)(s, "%s) THEN ", bitVectorModifier);
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, True);
      		l = VG_(sprintf)(s, " ELSE ");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
      		printSizedBool(size, False);
      		l = VG_(sprintf)(s, " ENDIF);\n");
		my_write(fdtrace, s, l);
		my_write(fddanger, s, l);
                break;
    default:	break;
  }
}

/*---------------------------------------------------------------------------*/
/*---------------------------instrumentWrTmpLongBinop------------------------*/
/*---------------------------------------------------------------------------*/

/* All actual instrumentation of WrTmp for long operations takes place in
   instrumentWrTmpLongBinop_Internal, which is common for {x86, amd64, ARM}. 

   instrumentWrTmpLongBinop_Internal is called by instrumentWrTmpLongBinop, 
   which is a dirty helper unique for {x86, amd64, ARM}.

   Call to instrumentWrTmpLongBinop is inserted to SuperBlock by
   instrumentWrTmpLongBinop_External which is unique for {x86, amd64, ARM}. */

void instrumentWrTmpLongBinop_Internal(UInt oprt, UInt ltmp,
                                       UShort taintedness,
                                       IRExpr* arg1, IRExpr* arg2,
                                       ULong value1, ULong value2)
{
  Char s[256];
  Int l = 0;
  UShort size = curNode->tempSize[ltmp];
  if ((oprt != Iop_Shr64) && (oprt != Iop_Sar64) && (oprt != Iop_Shl64))
  {
    taintTemp(ltmp);
  }
  switch (oprt)
  {
    case Iop_CmpEQ64:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF ", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    			 	translateLong1(arg1, value1, taintedness);
    				l = VG_(sprintf)(s, "=");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    				translateLong2(arg2, value2, taintedness);
    				l = VG_(sprintf)(s, " THEN ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
      				printSizedBool(size, True);
				l = VG_(sprintf)(s, " ELSE ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, False);
                                l = VG_(sprintf)(s, " ENDIF);\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    case Iop_CmpLT64S:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF SBVLT(", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    			 	translateLong1(arg1, value1, taintedness);
    				l = VG_(sprintf)(s, ", ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    				translateLong2(arg2, value2, taintedness);
    				l = VG_(sprintf)(s, ") THEN ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
      				printSizedBool(size, True);
                                l = VG_(sprintf)(s, " ELSE ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, False);
                                l = VG_(sprintf)(s, " ENDIF);\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    case Iop_CmpLT64U:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF BVLT(", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    			 	translateLong1(arg1, value1, taintedness);
    				l = VG_(sprintf)(s, ", ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    				translateLong2(arg2, value2, taintedness);
    				l = VG_(sprintf)(s, ") THEN ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
      				printSizedBool(size, True);
                                l = VG_(sprintf)(s, " ELSE ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, False);
                                l = VG_(sprintf)(s, " ENDIF);\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
     case Iop_CmpLE64S:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF SBVLE(", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    			 	translateLong1(arg1, value1, taintedness);
    				l = VG_(sprintf)(s, ", ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    				translateLong2(arg2, value2, taintedness);
    				l = VG_(sprintf)(s, ") THEN ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
      				printSizedBool(size, True);
                                l = VG_(sprintf)(s, " ELSE ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, False);
                                l = VG_(sprintf)(s, " ENDIF);\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    case Iop_CmpLE64U:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF BVLE(", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    			 	translateLong1(arg1, value1, taintedness);
    				l = VG_(sprintf)(s, ", ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    				translateLong2(arg2, value2, taintedness);
    				l = VG_(sprintf)(s, ") THEN ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
      				printSizedBool(size, True);
                                l = VG_(sprintf)(s, " ELSE ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, False);
                                l = VG_(sprintf)(s, " ENDIF);\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    case Iop_CmpNE64:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF NOT(", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    			 	translateLong1(arg1, value1, taintedness);
    				l = VG_(sprintf)(s, "=");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    				translateLong2(arg2, value2, taintedness);
    				l = VG_(sprintf)(s, ") THEN ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
      				printSizedBool(size, True);
                                l = VG_(sprintf)(s, " ELSE ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, False);
                                l = VG_(sprintf)(s, " ENDIF);\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    case Iop_Add64:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=BVPLUS(64,", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong1(arg1, value1, taintedness);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong2(arg2, value2, taintedness);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    case Iop_Sub64: 		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=BVSUB(64,", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong1(arg1, value1, taintedness);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong2(arg2, value2, taintedness);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    case Iop_Mul64: 		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=BVMULT(64,", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong1(arg1, value1, taintedness);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong2(arg2, value2, taintedness);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    case Iop_Or64: 		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong1(arg1, value1, taintedness);
				l = VG_(sprintf)(s, "|");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong2(arg2, value2, taintedness);
				l = VG_(sprintf)(s, ");\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    case Iop_And64: 		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong1(arg1, value1, taintedness);
				l = VG_(sprintf)(s, "&");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong2(arg2, value2, taintedness);
				l = VG_(sprintf)(s, ");\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    case Iop_Xor64: 		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=BVXOR(", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong1(arg1, value1, taintedness);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong2(arg2, value2, taintedness);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    case Iop_Sar64:		if (!firstTainted(taintedness))
				{
				  break;
				}
                                taintTemp(ltmp);
                                l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=SBVDIV(64,", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong1(arg1, value1, taintedness);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLongToPowerOfTwo(arg2, value2);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    case Iop_Shl64: 		if (!firstTainted(taintedness))
				{
				  return;
				}
                                value2 = getDecimalValue(arg2, value2);
				if (value2 == 0)
                                {
                                  taintTemp(ltmp);
                                  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", curblock, ltmp, curvisited);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
                                  translateLong1(arg1, value1, taintedness);
                                  l = VG_(sprintf)(s, ");\n");
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
                                }
/*				else if (value2 >= 64)
				{
				  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=0hex0000000000000000);\n", curblock, ltmp, curvisited);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
				}*/
                                else if (value2 < 64)
                                {
                                  taintTemp(ltmp);
				  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=(", curblock, ltmp, curvisited);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
				  translateLong1(arg1, value1, taintedness);
				  l = VG_(sprintf)(s, " << %llu)[63:0]);\n", value2);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
				}
				break;
    case Iop_Shr64: 		if (!firstTainted(taintedness))
				{
				  return;
				}
                                value2 = getDecimalValue(arg2, value2);
				if (value2 == 0)
                                {
                                  taintTemp(ltmp);
                                  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", curblock, ltmp, curvisited);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
                                  translateLong1(arg1, value1, taintedness);
                                  l = VG_(sprintf)(s, ");\n");
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
                                }
                                else
                                {
                                  taintTemp(ltmp);
				  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=(", curblock, ltmp, curvisited);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
				  translateLong1(arg1, value1, taintedness);
				  l = VG_(sprintf)(s, ">> %llu));\n", value2);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
				}
				break;
    case Iop_DivU64:		if (checkDanger && (arg2->tag == Iex_RdTmp) && secondTainted(taintedness) && (!enableFiltering || useFiltering()))
				{
				  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", curblock, arg2->Iex.RdTmp.tmp, curvisited);
				  my_write(fddanger, s, l);
				  printSizedBool_DangerOnly(curNode->tempSize[arg2->Iex.RdTmp.tmp], False);
				  l = VG_(sprintf)(s, ");\nQUERY(FALSE);\n");
                                  if (fdfuncFilter >= 0)
                                  {
                                    dumpCall();
                                  }
				  my_write(fddanger, s, l);
				}
				l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=BVDIV(64,", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong1(arg1, value1, taintedness);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong2(arg2, value2, taintedness);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    case Iop_DivS64:		if (checkDanger && (arg2->tag == Iex_RdTmp) && secondTainted(taintedness) && (!enableFiltering || useFiltering()))
				{
				  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", curblock, arg2->Iex.RdTmp.tmp, curvisited);
				  my_write(fddanger, s, l);
				  printSizedBool_DangerOnly(curNode->tempSize[arg2->Iex.RdTmp.tmp], False);
				  l = VG_(sprintf)(s, ");\nQUERY(FALSE);\n");
                                  if (fdfuncFilter >= 0)
                                  {
                                    dumpCall();
                                  }
				  my_write(fddanger, s, l);
				}
				l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=SBVDIV(64,", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong1(arg1, value1, taintedness);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateLong2(arg2, value2, taintedness);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
    }
}

/* In order for this to work on ARM we need to pass 64-bit value through 
   either r0;r1 or r2;r3 - that's why formal params are value2 and then value1.
*/

static
void instrumentWrTmpDivisionBinop(IRStmt* clone, HWord value2, ULong value1)
{
  IRExpr* arg1 = clone->Ist.WrTmp.data->Iex.Binop.arg1;
  IRExpr* arg2 = clone->Ist.WrTmp.data->Iex.Binop.arg2;
  UShort taintedness = isPropagation2(arg1, arg2);
  if (taintedness)
  {
    UInt ltmp = clone->Ist.WrTmp.tmp;
    UInt oprt = clone->Ist.WrTmp.data->Iex.Binop.op;
    Char s[256];
    Int l = 0;
    taintTemp(ltmp);
#ifdef TAINTED_TRACE_PRINTOUT
    ppIRStmt(clone);
    VG_(printf) ("\n");
#endif
    /* I64 x = DivMod(I64 a, I32 b): x_hi is a mod b, x_lo is a div b
       I64 x = sDivMod(I64, I32): signed version of above */
    if (checkDanger && (arg2->tag == Iex_RdTmp) && 
        secondTainted(taintedness) && (!enableFiltering || useFiltering()))
    {
      l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", 
                          curblock, arg2->Iex.RdTmp.tmp, curvisited);
      my_write(fddanger, s, l);
      printSizedBool_DangerOnly(curNode->tempSize[arg2->Iex.RdTmp.tmp], False);
      l = VG_(sprintf)(s, ");\nQUERY(FALSE);\n");
      if (fdfuncFilter >= 0)
      {
        dumpCall();
      }
      my_write(fddanger, s, l);
    }
    if (oprt == Iop_DivModU64to32)
    {
      l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=(BVMOD(64,", 
                          curblock, ltmp, curvisited);
    }
    else
    {
      l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=(SBVMOD(64,", 
                          curblock, ltmp, curvisited);
    }
    my_write(fdtrace, s, l);
    my_write(fddanger, s, l);
    translateLong1(arg1, value1, taintedness);
    l = VG_(sprintf)(s, ",(0hex00000000 @ ");
    my_write(fdtrace, s, l);
    my_write(fddanger, s, l);
    translate2(arg2, value2, taintedness);
    if (oprt == Iop_DivModU64to32)
    {
      l = VG_(sprintf)(s, "))[31:0] @ 0hex00000000) | (0hex00000000 @ BVDIV(64,");
    }
    else
    {
      l = VG_(sprintf)(s, "))[31:0] @ 0hex00000000) | (0hex00000000 @ SBVDIV(64,");
    }
    my_write(fdtrace, s, l);
    my_write(fddanger, s, l);
    translateLong1(arg1, value1, taintedness);
    l = VG_(sprintf)(s, ",(0hex00000000 @ ");
    my_write(fdtrace, s, l);
    my_write(fddanger, s, l);
    translate2(arg2, value2, taintedness);
    l = VG_(sprintf)(s, "))[31:0]));\n");
    my_write(fdtrace, s, l);
    my_write(fddanger, s, l);
  }
}

static
void instrumentWrTmpBinop(IRStmt* clone, HWord value1, HWord value2)
{
  IRExpr* arg1 = clone->Ist.WrTmp.data->Iex.Binop.arg1;
  IRExpr* arg2 = clone->Ist.WrTmp.data->Iex.Binop.arg2;
  UShort r = isPropagation2(arg1, arg2);
  UInt ltmp = clone->Ist.WrTmp.tmp;
  UInt oprt = clone->Ist.WrTmp.data->Iex.Binop.op;
  if (r)
  {
    Char s[256];
    Int l = 0;
    ULong sarg;
    UShort size = curNode->tempSize[ltmp];
    taintTemp(ltmp);
#ifdef TAINTED_TRACE_PRINTOUT
    ppIRStmt(clone);
    VG_(printf) ("\n");
#endif
    switch (oprt)
    {
      case Iop_CmpEQ8:
      case Iop_CmpEQ16:
      case Iop_CmpEQ32:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF ", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    			 	translate1(arg1, value1, r);
    				l = VG_(sprintf)(s, "=");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    				translate2(arg2, value2, r);
    				l = VG_(sprintf)(s, " THEN ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, True);
                                l = VG_(sprintf)(s, " ELSE ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, False);
                                l = VG_(sprintf)(s, " ENDIF);\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_CmpLT32S:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF SBVLT(", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    			 	translate1(arg1, value1, r);
    				l = VG_(sprintf)(s, ", ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    				translate2(arg2, value2, r);
    				l = VG_(sprintf)(s, ") THEN ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, True);
                                l = VG_(sprintf)(s, " ELSE ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, False);
                                l = VG_(sprintf)(s, " ENDIF);\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_CmpLT32U:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF BVLT(", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    			 	translate1(arg1, value1, r);
    				l = VG_(sprintf)(s, ", ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    				translate2(arg2, value2, r);
    				l = VG_(sprintf)(s, ") THEN ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, True);
                                l = VG_(sprintf)(s, " ELSE ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, False);
                                l = VG_(sprintf)(s, " ENDIF);\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_CmpLE32S:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF SBVLE(", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    			 	translate1(arg1, value1, r);
    				l = VG_(sprintf)(s, ", ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    				translate2(arg2, value2, r);
    				l = VG_(sprintf)(s, ") THEN ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, True);
                                l = VG_(sprintf)(s, " ELSE ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, False);
                                l = VG_(sprintf)(s, " ENDIF);\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_CmpLE32U:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF BVLE(", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    			 	translate1(arg1, value1, r);
    				l = VG_(sprintf)(s, ", ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    				translate2(arg2, value2, r);
    				l = VG_(sprintf)(s, ") THEN ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, True);
                                l = VG_(sprintf)(s, " ELSE ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, False);
                                l = VG_(sprintf)(s, " ENDIF);\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;

      case Iop_CmpNE8:
      case Iop_CmpNE16:
      case Iop_CmpNE32:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=IF NOT(", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    			 	translate1(arg1, value1, r);
    				l = VG_(sprintf)(s, "=");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
    				translate2(arg2, value2, r);
    				l = VG_(sprintf)(s, ") THEN ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, True);
                                l = VG_(sprintf)(s, " ELSE ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
                                printSizedBool(size, False);
                                l = VG_(sprintf)(s, " ENDIF);\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_Add8:
      case Iop_Add16:
      case Iop_Add32:		if (oprt == Iop_Add8) size = 8;
				else if (oprt == Iop_Add16) size = 16;
				else size = 32;
				l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=BVPLUS(%u,", curblock, ltmp, curvisited, size);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate1(arg1, value1, r);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate2(arg2, value2, r);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_Sub8:
      case Iop_Sub16:
      case Iop_Sub32:		if (oprt == Iop_Sub8) size = 8;
				else if (oprt == Iop_Sub16) size = 16;
				else size = 32;
				l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=BVSUB(%u,", curblock, ltmp, curvisited, size);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate1(arg1, value1, r);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate2(arg2, value2, r);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_Mul8:
      case Iop_Mul16:
      case Iop_Mul32:		if (oprt == Iop_Mul8) size = 8;
				else if (oprt == Iop_Mul16) size = 16;
				else size = 32;
				l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=BVMULT(%u,", curblock, ltmp, curvisited, size);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate1(arg1, value1, r);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate2(arg2, value2, r);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_Or8:
      case Iop_Or16:
      case Iop_Or32:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate1(arg1, value1, r);
				l = VG_(sprintf)(s, "|");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate2(arg2, value2, r);
				l = VG_(sprintf)(s, ");\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_And8:
      case Iop_And16:
      case Iop_And32:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate1(arg1, value1, r);
				l = VG_(sprintf)(s, "&");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate2(arg2, value2, r);
				l = VG_(sprintf)(s, ");\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_Xor8:
      case Iop_Xor16:
      case Iop_Xor32:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=BVXOR(", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate1(arg1, value1, r);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate2(arg2, value2, r);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;

      case Iop_Sar8:
      case Iop_Sar16:
      case Iop_Sar32:		if (secondTainted(r))
				{
				  //break;
				}
				if (oprt == Iop_Sar8) size = 8;
				else if (oprt == Iop_Sar16) size = 16;
				else if (oprt == Iop_Sar32) size = 32;
				else size = 64;
				l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=SBVDIV(%u,", curblock, ltmp, curvisited, size);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate1(arg1, value1, r);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translateToPowerOfTwo(arg2, value2, size);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_Shl8:
      case Iop_Shl16:
      case Iop_Shl32:		if (secondTainted(r))
				{
				  //break;
				}
				if (oprt == Iop_Shl8) size = 8;
				else if (oprt == Iop_Shl16) size = 16;
				else size = 32;
				sarg = getDecimalValue(arg2, value2);
				if (sarg == 0)
                                {
                                  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", curblock, ltmp, curvisited);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
                                  translate1(arg1, value1, r);
                                  l = VG_(sprintf)(s, ");\n");
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
                                }
                                else
                                {
				  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=(", curblock, ltmp, curvisited);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
				  translate1(arg1, value1, r);
				  l = VG_(sprintf)(s, " << %llu)", sarg);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
				  l = VG_(sprintf)(s, "[%u:0]);\n", size - 1);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
				}
				break;
      case Iop_Shr8:
      case Iop_Shr16:
      case Iop_Shr32:		if (secondTainted(r))
				{
				  //break;
				}
				sarg = getDecimalValue(arg2, value2);
				if (sarg == 0)
                                {
                                  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", curblock, ltmp, curvisited);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
                                  translate1(arg1, value1, r);
                                  l = VG_(sprintf)(s, ");\n");
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
                                }
                                else
                                {
				  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=(", curblock, ltmp, curvisited);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
				  translate1(arg1, value1, r);
				  l = VG_(sprintf)(s, ">> %llu));\n", sarg);
				  my_write(fdtrace, s, l);
				  my_write(fddanger, s, l);
				}
				break;
      case Iop_DivU32:		if (checkDanger && (arg2->tag == Iex_RdTmp) && secondTainted(r) && (!enableFiltering || useFiltering()))
				{
				  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", curblock, arg2->Iex.RdTmp.tmp, curvisited);
				  my_write(fddanger, s, l);
				  printSizedBool_DangerOnly(curNode->tempSize[arg2->Iex.RdTmp.tmp], False);
				  l = VG_(sprintf)(s, ");\nQUERY(FALSE);\n");
                                  if (fdfuncFilter >= 0)
                                  {
                                    dumpCall();
                                  }
				  my_write(fddanger, s, l);
				}
				l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=BVDIV(32,", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate1(arg1, value1, r);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate2(arg2, value2, r);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_DivS32:		if (checkDanger && (arg2->tag == Iex_RdTmp) && secondTainted(r) && (!enableFiltering || useFiltering()))
				{
				  l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", curblock, arg2->Iex.RdTmp.tmp, curvisited);
				  my_write(fddanger, s, l);
				  printSizedBool_DangerOnly(curNode->tempSize[arg2->Iex.RdTmp.tmp], False);
				  l = VG_(sprintf)(s, ");\nQUERY(FALSE);\n");
                                  if (fdfuncFilter >= 0)
                                  {
                                    dumpCall();
                                  }
      				  my_write(fddanger, s, l);
				}
				l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=SBVDIV(32,", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate1(arg1, value1, r);
				l = VG_(sprintf)(s, ",");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate2(arg2, value2, r);
				l = VG_(sprintf)(s, "));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_8HLto16:		l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=((", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate1(arg1, value1, r);
				l = VG_(sprintf)(s, " @ 0hex00) | (0hex00 @ ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate2(arg2, value2, r);
				l = VG_(sprintf)(s, ")));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_16HLto32:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=((", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate1(arg1, value1, r);
				l = VG_(sprintf)(s, " @ 0hex0000) | (0hex0000 @ ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate2(arg2, value2, r);
				l = VG_(sprintf)(s, ")));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      case Iop_32HLto64:	l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=((", curblock, ltmp, curvisited);
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate1(arg1, value1, r);
				l = VG_(sprintf)(s, " @ 0hex00000000) | (0hex00000000 @ ");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				translate2(arg2, value2, r);
				l = VG_(sprintf)(s, ")));\n");
				my_write(fdtrace, s, l);
				my_write(fddanger, s, l);
				break;
      /* Widening multiplies: */
      case Iop_MullU8: // I16 = I8 x I8
      case Iop_MullU16: // I32 = I16 x I16
      case Iop_MullU32: // I64 = I32 x I32
                l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=BVMULT(%u,(", 
                                    curblock, ltmp, curvisited, size);
                my_write(fdtrace, s, l);
                my_write(fddanger, s, l);
                printSizedBool(size >> 1, False);
                l = VG_(sprintf)(s, " @ ");
                my_write(fdtrace, s, l);
                my_write(fddanger, s, l);
                translate1(arg1, value1, r);
                l = VG_(sprintf)(s, "),(");
                my_write(fdtrace, s, l);
                my_write(fddanger, s, l);
                printSizedBool(size >> 1, False);
                l = VG_(sprintf)(s, " @ ");
                my_write(fdtrace, s, l);
                my_write(fddanger, s, l);
                translate2(arg2, value2, r);
                l = VG_(sprintf)(s, ")));\n");
                my_write(fdtrace, s, l);
                my_write(fddanger, s, l);
                break;
      default: 			break;
    }
  }
}

static
void instrumentStoreGet(IRStmt* clone, IRExpr* storeAddr, UInt offset)
{
  UShort size;
  switch (clone->Ist.Store.data->Iex.Get.ty)
  {
    case Ity_I8:	size = 8;
			break;
    case Ity_I16:	size = 16;
			break;
    case Ity_I32:	size = 32;
			break;
    case Ity_I64:	size = 64;
			break;
    default:        return;
  }
  UWord addr = (UWord) storeAddr;
  if (VG_(HT_lookup)(taintedRegisters, offset) != NULL)
  {
    taintMemory(addr, size);
#ifdef TAINTED_TRACE_PRINTOUT
    ppIRStmt(clone);
    VG_(printf) ("\n");
#endif
    Char ss[256];
    Int l = 0;
    switch (size)
    {
      case 8:	l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 1, memory, addr, registers, offset);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                memory++;
                break;
      case 16:	l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 1, memory, addr, registers, offset);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 2, memory + 1, addr + 1, registers, offset + 1);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                memory += 2;
                break;
      case 32:  l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 1, memory, addr, registers, offset);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 2, memory + 1, addr + 1, registers, offset + 1);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 3, memory + 2, addr + 2, registers, offset + 2);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 4, memory + 3, addr + 3, registers, offset + 3);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                memory += 4;
                break;
      case 64:  l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 1, memory, addr, registers, offset);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 2, memory + 1, addr + 1, registers, offset + 1);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 3, memory + 2, addr + 2, registers, offset + 2);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 4, memory + 3, addr + 3, registers, offset + 3);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 5, memory + 4, addr + 4, registers, offset + 4);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 6, memory + 5, addr + 5, registers, offset + 5);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 7, memory + 6, addr + 6, registers, offset + 6);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := registers_%d[0hex%02x];\n", memory + 8, memory + 7, addr + 7, registers, offset + 7);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                memory += 8;
                break;
      default:	break;
    }
  }
  else
  {
    untaintMemory(addr, size);
  }
}

static
void instrumentStoreRdTmp(IRStmt* clone, IRExpr* storeAddr, UInt tmp)
{
  UShort size = curNode->tempSize[tmp];
  UWord addr = (UWord) storeAddr;

  /* This shouldn't work properly without am_get_client_segment_starts,
     better remove it. Also address is not guaranteed to be in a temporary
     anymore, it can be a number - (check issue 7 on googlecode). */

  /* if (checkDanger && (VG_(HT_lookup)(taintedTemps, ltmp) != NULL) && (!enableFiltering || useFiltering()))
  {
    Char s[256];
    Int l = 0;
    Addr addrs[256];
    //Int segs = VG_(am_get_client_segment_starts)(addrs, 256);
    NSegment* seg = VG_(am_find_nsegment)(addrs[0]);
    Char format[256];
    VG_(sprintf)(format, "ASSERT(BVLT(t_%%lx_%%u_%%u, 0hex%%0%ux));\nQUERY(FALSE);\n",
                 curNode->tempSize[ltmp] / 4);
    if (fdfuncFilter >= 0)
    {
      dumpCall();
    }
    l = VG_(sprintf)(s, format, curblock, ltmp, curvisited, seg->start);
    my_write(fddanger, s, l);
  } */

  if (VG_(HT_lookup)(taintedTemps, tmp) != NULL)
  {
    taintMemory(addr, size);
#ifdef TAINTED_TRACE_PRINTOUT
    ppIRStmt(clone);
    VG_(printf) ("\n");
#endif
    Char ss[256];
    Int l = 0;
    switch (curNode->tempSize[tmp])
    {
      case 8:	l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u;\n", memory + 1, memory, addr, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                memory++;
                break;
      case 16:	l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[7:0];\n", memory + 1, memory, addr, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[15:8];\n", memory + 2, memory + 1, addr + 1, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                memory += 2;
                break;
      case 32:  l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[7:0];\n", memory + 1, memory, addr, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[15:8];\n", memory + 2, memory + 1, addr + 1, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[23:16];\n", memory + 3, memory + 2, addr + 2, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[31:24];\n", memory + 4, memory + 3, addr + 3, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                memory += 4;
                break;
      case 64:  l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[7:0];\n", memory + 1, memory, addr, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[15:8];\n", memory + 2, memory + 1, addr + 1, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[23:16];\n", memory + 3, memory + 2, addr + 2, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[31:24];\n", memory + 4, memory + 3, addr + 3, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[39:32];\n", memory + 5, memory + 4, addr + 4, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[47:40];\n", memory + 6, memory + 5, addr + 5, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[55:48];\n", memory + 7, memory + 6, addr + 6, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                l = VG_(sprintf)(ss, "memory_%d : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8) = memory_%d WITH [0hex" PTR_FMT "] := t_%lx_%u_%u[63:56];\n", memory + 8, memory + 7, addr + 7, curblock, tmp, curvisited);
                my_write(fdtrace, ss, l);
		my_write(fddanger, ss, l);
                memory += 8;
                break;
      default:	break;
    }
  }
  else
  {
    untaintMemory(addr, size);
  }
}

static
void instrumentStoreConst(IRStmt* clone, IRExpr* addr)
{
  UShort size;
  switch (clone->Ist.Store.data->Iex.Const.con->tag)
  {
    case Ico_U8:	size = 8;
			break;
    case Ico_U16:	size = 16;
			break;
    case Ico_U32:	size = 32;
			break;
    case Ico_U64:	size = 64;
			break;
    default:        return;
  }
  untaintMemory((UWord) addr, size);
}

static
void instrumentExitRdTmp(IRStmt* clone, HWord guard, UInt tmp, ULong dst)
{
  if ((VG_(HT_lookup)(taintedTemps, tmp) != NULL) && (!enableFiltering || useFiltering()))
  {
#ifdef TAINTED_TRACE_PRINTOUT
    ppIRStmt(clone);
    VG_(printf) ("\n");
#endif
    Char s[256];
    Int l = VG_(sprintf)(s, "ASSERT(t_%lx_%u_%u=", curblock, tmp, curvisited);
    my_write(fdtrace, s, l);
    my_write(fddanger, s, l);
    if (dumpPrediction)
    {
      actual[curdepth] = (Bool) guard;
    }
    if (guard == 1)
    {
      printSizedBool(curNode->tempSize[tmp], True);
    }
    else
    {
      printSizedBool(curNode->tempSize[tmp], False);
    }
    if (checkPrediction && !divergence && (curdepth < depth) && ((Bool) guard != prediction[curdepth]))
    {
      Char* divergenceFile = concatTempDir("divergence.log");
      SysRes fd = VG_(open)(divergenceFile, VKI_O_WRONLY | VKI_O_TRUNC | VKI_O_CREAT, PERM_R_W);
      divergence = True;
      VG_(write)(sr_Res(fd), &divergence, sizeof(Bool));
      VG_(write)(sr_Res(fd), &curdepth, sizeof(Int));
      VG_(close)(sr_Res(fd));
      VG_(free)(divergenceFile);
    }
    l = VG_(sprintf)(s, ");\n");
    my_write(fdtrace, s, l);
    my_write(fddanger, s, l);
    if (checkPrediction && (curdepth == depth) && !divergence)
    {
      Char* divergenceFile = concatTempDir("divergence.log");
      SysRes fd = VG_(open)(divergenceFile, VKI_O_WRONLY | VKI_O_TRUNC | VKI_O_CREAT, PERM_R_W);
      divergence = False;
      VG_(write)(sr_Res(fd), &divergence, sizeof(Bool));
      VG_(close)(sr_Res(fd));
      VG_(free)(divergenceFile);
    }
    if (curdepth >= depth)
    {
      l = VG_(sprintf)(s, "QUERY(FALSE);\n");
      if (fdfuncFilter >= 0)
      {
        dumpCall();
      }
      my_write(fdtrace, s, l);
    }
    curdepth++;
    if (!noInvertLimit && (curdepth > depth + invertdepth) && (fdfuncFilter == -1))
    {
      dump(fdtrace);
      dump(fddanger);
      if (dumpChunkSize)
      {
        Int size = 0;
        VG_(write)(fdtrace, &size, sizeof(Int));
      }
      if (dumpPrediction)
      {
        Char* actualFile = concatTempDir("actual.log");
        SysRes fd = VG_(open)(actualFile, VKI_O_WRONLY | VKI_O_TRUNC | VKI_O_CREAT, PERM_R_W);
        VG_(write)(sr_Res(fd), actual, (depth + invertdepth) * sizeof(Bool));
        VG_(close)(sr_Res(fd));
        VG_(free)(actualFile);
      }
      if (replace)
      {
        Char* replaceFile = concatTempDir("replace_data");
        Int fd = sr_Res(VG_(open)(replaceFile, VKI_O_WRONLY, PERM_R_W));
        VG_(write)(fd, &socketsNum, 4);
        Int i;
        for (i = 0; i < socketsNum; i++)
        {
          VG_(write)(fd, &(replace_data[i].length), sizeof(Int));
          VG_(write)(fd, replace_data[i].data, replace_data[i].length);
        }
        VG_(close)(fd);
        VG_(free)(replaceFile);
      }
      Char* offsetFile = concatTempDir("offsets.log");
      storeUsedOffsets(offsetFile);
      VG_(free)(offsetFile);
      VG_(exit)(0);
    }
  }
}

static
void instrumentPut(IRStmt* clone, IRSB* sbOut)
{
  IRDirty* di;
  UInt offset = clone->Ist.Put.offset;
  IRExpr* data = clone->Ist.Put.data;
  switch (data->tag)
  {
    case Iex_Load: 	di = unsafeIRDirty_0_N(0, "instrumentPutLoad",
						VG_(fnptr_to_fnentry)(&instrumentPutLoad), 
						mkIRExprVec_3(mkIRExpr_HWord((HWord)  clone), 
								mkIRExpr_HWord(offset), data->Iex.Load.addr));
                   	addStmtToIRSB(sbOut, IRStmt_Dirty(di));
                   	break;
    case Iex_Get:      	di = unsafeIRDirty_0_N(0, "instrumentPutGet",
						VG_(fnptr_to_fnentry)(&instrumentPutGet), 
						mkIRExprVec_3(mkIRExpr_HWord((HWord) clone), mkIRExpr_HWord(offset), 
								mkIRExpr_HWord(data->Iex.Get.offset)));
                   	addStmtToIRSB(sbOut, IRStmt_Dirty(di));
                   	break;
    case Iex_RdTmp:    	di = unsafeIRDirty_0_N(0, "instrumentPutRdTmp", 
						VG_(fnptr_to_fnentry)(&instrumentPutRdTmp), 
						mkIRExprVec_3(mkIRExpr_HWord((HWord) clone), mkIRExpr_HWord(offset), 
								mkIRExpr_HWord(data->Iex.RdTmp.tmp)));
                   	addStmtToIRSB(sbOut, IRStmt_Dirty(di));
                   	break;
    case Iex_Const:	di = unsafeIRDirty_0_N(0, "instrumentPutConst",
						VG_(fnptr_to_fnentry)(&instrumentPutConst), 
						mkIRExprVec_2(mkIRExpr_HWord((HWord) clone), mkIRExpr_HWord(offset)));
                   	addStmtToIRSB(sbOut, IRStmt_Dirty(di));
                   	break;
    default:		break;
  }
}

static
void instrumentWrTmp(IRStmt* clone, IRSB* sbOut, IRTypeEnv* tyenv)
{
  IRDirty* di;
  IRExpr* arg0, * arg1,* arg2,* arg3;
  UInt tmp = clone->Ist.WrTmp.tmp;
  IRExpr* data = clone->Ist.WrTmp.data;
  IRExpr* value0, *value1,* value2, * value3;
  Int size = 0;
  switch (data->tag)
  {
    case Iex_Load:
       di = unsafeIRDirty_0_N(0, "instrumentWrTmpLoad", 
                              VG_(fnptr_to_fnentry)(&instrumentWrTmpLoad),
                              mkIRExprVec_2(mkIRExpr_HWord((HWord) clone), 
                                            data->Iex.Load.addr));
       addStmtToIRSB(sbOut, IRStmt_Dirty(di));
       break;

    case Iex_Get:
       di = unsafeIRDirty_0_N(0, "instrumentWrTmpGet", 
                              VG_(fnptr_to_fnentry)(&instrumentWrTmpGet),
                              mkIRExprVec_3(mkIRExpr_HWord((HWord) clone),
                                            mkIRExpr_HWord(tmp),
                                            mkIRExpr_HWord(data->Iex.Get.offset)));
       addStmtToIRSB(sbOut, IRStmt_Dirty(di));
       break;

    case Iex_RdTmp:
       di = unsafeIRDirty_0_N(0, "instrumentWrTmpRdTmp",
                              VG_(fnptr_to_fnentry)(&instrumentWrTmpRdTmp), 
                              mkIRExprVec_3(mkIRExpr_HWord((HWord) clone),
                                            mkIRExpr_HWord(tmp), 
                                            mkIRExpr_HWord(data->Iex.RdTmp.tmp)));
       addStmtToIRSB(sbOut, IRStmt_Dirty(di));
       break;

    case Iex_Unop:
       if (data->Iex.Unop.arg->tag == Iex_RdTmp)
       {
         IRExpr* _arg3 = mkIRExpr_HWord(data->Iex.Unop.arg->Iex.RdTmp.tmp);
         di = unsafeIRDirty_0_N(0, "instrumentWrTmpUnop", 
                                VG_(fnptr_to_fnentry)(&instrumentWrTmpUnop), 
                                mkIRExprVec_4(mkIRExpr_HWord((HWord) clone),  
                                              mkIRExpr_HWord(tmp), _arg3,
                                              mkIRExpr_HWord(data->Iex.Unop.op)));
         addStmtToIRSB(sbOut, IRStmt_Dirty(di));
       }
       break;

    case Iex_Binop:
       arg1 = data->Iex.Binop.arg1;
       arg2 = data->Iex.Binop.arg2;
       value1 = adjustSize(sbOut, tyenv, arg1);
       value2 = adjustSize(sbOut, tyenv, arg2);
       IROp op = data->Iex.Binop.op;
       if ((op == Iop_CmpLT64S) || (op == Iop_CmpLT64U) || (op == Iop_Or64)  ||
           (op == Iop_CmpLE64S) || (op == Iop_CmpLE64U) || (op == Iop_And64) ||
           (op == Iop_CmpEQ64)  || (op == Iop_CmpNE64)  || (op == Iop_Xor64) ||
           (op == Iop_Add64)    || (op == Iop_Sub64)    || (op == Iop_Mul64) ||
           (op == Iop_Sar64)    || (op == Iop_Shl64)    || (op == Iop_Shr64) ||
           (op == Iop_DivU64)   || (op == Iop_DivS64))
       {
         instrumentWrTmpLongBinop_External(sbOut, clone, value1, value2);
       }

       else if ((op == Iop_DivModU64to32) || (op == Iop_DivModS64to32))
       {
         di = unsafeIRDirty_0_N(0, "instrumentWrTmpDivisionBinop", 
                                VG_(fnptr_to_fnentry)(&instrumentWrTmpDivisionBinop),
                                mkIRExprVec_3(mkIRExpr_HWord((HWord) clone), 
                                                             value2, value1));
         addStmtToIRSB(sbOut, IRStmt_Dirty(di));
       }

       /* Do not try to instrument floating point operations */
       else if ((op - Iop_INVALID <= 128) &&
                (typeOfIRExpr(tyenv, arg1) - Ity_INVALID <= 5) &&
                (typeOfIRExpr(tyenv, arg2) - Ity_INVALID <= 5))
       {
         di = unsafeIRDirty_0_N(0, "instrumentWrTmpBinop", 
                                VG_(fnptr_to_fnentry)(&instrumentWrTmpBinop), 
                                mkIRExprVec_3(mkIRExpr_HWord((HWord) clone),
                                              value1, value2));
         addStmtToIRSB(sbOut, IRStmt_Dirty(di));
       }
       break;

    case Iex_Mux0X:
       arg0 = data->Iex.Mux0X.cond;
       arg1 = data->Iex.Mux0X.expr0;
       arg2 = data->Iex.Mux0X.exprX;
       if ((typeOfIRExpr(tyenv, arg0) - Ity_INVALID <= 5) &&
           (typeOfIRExpr(tyenv, arg1) - Ity_INVALID <= 5) &&
           (typeOfIRExpr(tyenv, arg2) - Ity_INVALID <= 5))
       {

         value0 = adjustSize(sbOut, tyenv, arg0);
         value1 = adjustSize(sbOut, tyenv, arg1);
         value2 = adjustSize(sbOut, tyenv, arg2);
         di = unsafeIRDirty_0_N(0, "instrumentWrTmpMux0X",
                                VG_(fnptr_to_fnentry)(&instrumentWrTmpMux0X),
                                mkIRExprVec_4(mkIRExpr_HWord((HWord) clone), 
                                              value0, value1, value2));
         addStmtToIRSB(sbOut, IRStmt_Dirty(di));
       }
       break;

    case Iex_CCall:
       for (; data->Iex.CCall.args[size ++] != NULL;);
       arg0 = (size > 0) ? data->Iex.CCall.args[0] : NULL;
       arg1 = (size > 1) ? data->Iex.CCall.args[1] : NULL;
       arg2 = (size > 2) ? data->Iex.CCall.args[2] : NULL;
       arg3 = (size > 3) ? data->Iex.CCall.args[3] : NULL;
       
       value0 = adjustSize(sbOut, tyenv, arg0);
       value1 = adjustSize(sbOut, tyenv, arg1);
       value2 = adjustSize(sbOut, tyenv, arg2);
       value3 = adjustSize(sbOut, tyenv, arg3);
       instrumentWrTmpCCall_External(sbOut, clone, 
                                     value0, value1, value2, value3);
       break;

    default: break;
  }
}

static
void instrumentStore(IRStmt* clone, IRSB* sbOut)
{
  IRDirty* di;
  IRExpr* addr = clone->Ist.Store.addr;
  IRExpr* data = clone->Ist.Store.data;
  switch (data->tag)
  {
    case Iex_Get:  	
       di = unsafeIRDirty_0_N(0, "instrumentStoreGet", 
                              VG_(fnptr_to_fnentry)(&instrumentStoreGet), 
                              mkIRExprVec_3(mkIRExpr_HWord((HWord) clone), addr, 
                                            mkIRExpr_HWord(data->Iex.Get.offset)));
       addStmtToIRSB(sbOut, IRStmt_Dirty(di));
       break;

    case Iex_RdTmp:
       di = unsafeIRDirty_0_N(0, "instrumentStoreRdTmp", 
                              VG_(fnptr_to_fnentry)(&instrumentStoreRdTmp), 
                              mkIRExprVec_3(mkIRExpr_HWord((HWord) clone), addr, 
                                            mkIRExpr_HWord(data->Iex.RdTmp.tmp)));
       addStmtToIRSB(sbOut, IRStmt_Dirty(di));
       break;

    case Iex_Const:
       di = unsafeIRDirty_0_N(0, "instrumentStoreConst", 
                              VG_(fnptr_to_fnentry)(&instrumentStoreConst), 
                              mkIRExprVec_2(mkIRExpr_HWord((HWord) clone), addr));
       addStmtToIRSB(sbOut, IRStmt_Dirty(di));
       break;

    default: break;
  }
}

static
void instrumentExit(IRStmt* clone, IRSB* sbOut, IRTypeEnv* tyenv)
{
  IRExpr* guard = clone->Ist.Exit.guard;
  ULong dst = clone->Ist.Exit.dst->Ico.U64;
  if (guard->tag == Iex_RdTmp)
  {
    IRExpr* etemp = adjustSize(sbOut, tyenv, guard);
    IRDirty* di = 
         unsafeIRDirty_0_N(0, "instrumentExitRdTmp", 
                           VG_(fnptr_to_fnentry)(&instrumentExitRdTmp), 
                           mkIRExprVec_4(mkIRExpr_HWord((HWord) clone), 
                                         etemp, 
                                         mkIRExpr_HWord(guard->Iex.RdTmp.tmp),
                                         mkIRExpr_HWord(dst)));
    addStmtToIRSB(sbOut, IRStmt_Dirty(di));
  }
}

static
void createTaintedTemp(UInt basicBlockLowerBytes, UInt basicBlockUpperBytes)
{
  curNode = VG_(HT_lookup)(tempSizeTable, basicBlockLowerBytes);
  curNode->visited++;
  curvisited = curNode->visited - 1;
  curblock = basicBlockLowerBytes;
  if (taintedTemps != NULL)
  {
    VG_(HT_destruct)(taintedTemps);
  }
  taintedTemps = VG_(HT_construct)("taintedTemps");
}

static
IRSB* tg_instrument(VgCallbackClosure* closure,
                    IRSB* sbIn,
                    VexGuestLayout* layout,
                    VexGuestExtents* vge,
                    IRType gWordTy, IRType hWordTy)
{
   IRTypeEnv* tyenv = sbIn->tyenv;
   Int i = 0;
   IRDirty* di;
   IRSB* sbOut;

   if (gWordTy != hWordTy) {
      /* We don't currently support this case. */
      VG_(tool_panic)("host/guest word size mismatch");
   }

   /* Set up SB */
   sbOut = deepCopyIRSBExceptStmts(sbIn);

   curblock = vge->base[0];

   curNode = VG_(malloc)("taintMemoryNode", sizeof(sizeNode));
   curNode->key = curblock;
   curNode->tempSize = VG_(malloc)("temps", tyenv->types_used * sizeof(UShort));
   for (i = 0; i < tyenv->types_used; i++)
   {
     if (tyenv->types[i] == Ity_I1)
     {
         curNode->tempSize[i] = 1;
     }
     else
     {
         curNode->tempSize[i] = sizeofIRType(tyenv->types[i]) << 3;
     }
   }
   curNode->visited = 0;
   VG_(HT_add_node)(tempSizeTable, curNode);

   curvisited = 0;
   UInt basicBlockUpperBytes, basicBlockLowerBytes;
   basicBlockUpperBytes = (vge->base[0] & 0xffffffff00000000ULL) >> 32;
   basicBlockLowerBytes = vge->base[0] & 0x00000000ffffffffULL;
   HWord iAddr;

   i = 0;
   di = unsafeIRDirty_0_N(0, "createTaintedTemp", VG_(fnptr_to_fnentry)(&createTaintedTemp), mkIRExprVec_2(mkIRExpr_HWord(vge->base[0]), mkIRExpr_HWord(basicBlockUpperBytes)));
   addStmtToIRSB(sbOut, IRStmt_Dirty(di));
   for (;i < sbIn->stmts_used; i++)
   {
     IRStmt* clone = deepMallocIRStmt((IRStmt*) sbIn->stmts[i]);
     switch (sbIn->stmts[i]->tag)
     {
       case Ist_IMark:
         iAddr = sbIn->stmts[i]->Ist.IMark.addr;
         di = unsafeIRDirty_0_N(0, "instrumentIMark", 
                                VG_(fnptr_to_fnentry)(&instrumentIMark), 
                                mkIRExprVec_1(mkIRExpr_HWord(iAddr)));
         addStmtToIRSB(sbOut, IRStmt_Dirty(di));
         break;
       case Ist_Put:
         instrumentPut(clone, sbOut);
         break;
       case Ist_WrTmp:
         instrumentWrTmp(clone, sbOut, sbOut->tyenv);
         break;
       case Ist_Store:
         instrumentStore(clone, sbOut);
         break;
       case Ist_Exit:
         instrumentExit(clone, sbOut, sbOut->tyenv);
         break;
       default: break;
     }
     addStmtToIRSB(sbOut, sbIn->stmts[i]);
   }
   return sbOut;
}

static void tg_fini(Int exitcode)
{
  dump(fdtrace);
  dump(fddanger);
  if (dumpChunkSize)
  {
    Int size = 0;
    VG_(write)(fdtrace, &size, sizeof(Int));
  }
  if (fdfuncFilter >= 0)
  {
    dump(fdfuncFilter);
  }
  if (dumpPrediction)
  {
    Char* actualFile = concatTempDir("actual.log");
    SysRes fd = VG_(open)(actualFile, VKI_O_WRONLY | VKI_O_TRUNC | VKI_O_CREAT, PERM_R_W);
    if (noInvertLimit)
    {
      curdepth --;
      VG_(write)(sr_Res(fd), &curdepth, sizeof(Int));
    }
    VG_(write)(sr_Res(fd), actual, (depth + invertdepth) * sizeof(Bool));
    VG_(close)(sr_Res(fd));
    VG_(free)(actualFile);
  }
  if (checkPrediction && !divergence)
  {
    Char* divergenceFile = concatTempDir("divergence.log");
    SysRes fd = VG_(open)(divergenceFile, VKI_O_WRONLY | VKI_O_TRUNC | VKI_O_CREAT, PERM_R_W);
    divergence = False;
    VG_(write)(sr_Res(fd), &divergence, sizeof(Bool));
    VG_(close)(sr_Res(fd));
    VG_(free)(divergenceFile);
  }
  if (replace)
  {
    Char* replaceFile = concatTempDir("replace_data");
    Int fd = sr_Res(VG_(open)(replaceFile, VKI_O_WRONLY, PERM_R_W));
    VG_(write)(fd, &socketsNum, 4);
    Int i;
    for (i = 0; i < socketsNum; i++)
    {
      VG_(write)(fd, &(replace_data[i].length), sizeof(Int));
      VG_(write)(fd, replace_data[i].data, replace_data[i].length);
    }
    VG_(close)(fd);
    VG_(free)(replaceFile);
  }
  if (fdfuncFilter >= 0) 
  {
    VG_(close)(fdfuncFilter);
  }
  Char* offsetFile = concatTempDir("offsets.log");
  storeUsedOffsets(offsetFile);
  VG_(free)(offsetFile);
//  if (inputFilterEnabled) 
//  {
//    VG_(deleteXA)(inputFilter);
//  }
}

Int filenum = 0;

static Bool tg_process_cmd_line_option(Char* arg)
{
  Char* argValue;
  if (VG_INT_CLO(arg, "--startdepth", depth))
  {
    depth -= 1;
    return True;
  }
  else if (VG_INT_CLO(arg, "--remote-fd", socketfd))
  {
    dumpChunkSize = True;
    return True;
  }
  else if (VG_INT_CLO(arg, "--invertdepth", invertdepth))
  {
    if (invertdepth == 0)
    {
      noInvertLimit = True;
    }
    return True;
  }
  else if (VG_STR_CLO(arg, "--port", argValue))
  {
    port = (UShort) VG_(strtoll10)(argValue, NULL);
    return True;
  }
  else if (VG_STR_CLO(arg, "--func-name", argValue))
  {
    parseFnName(argValue);
    enableFiltering = True;
    return True;
  }
  else if (VG_STR_CLO(arg, "--func-filter-file", argValue))
  {
    Int fd = sr_Res(VG_(open)(argValue, VKI_O_RDWR, 0));
    parseFuncFilterFile(fd);
    enableFiltering = True;
    VG_(close)(fd);
    return True;
  }
  else if (VG_STR_CLO(arg, "--temp-dir", tempDir))
  {
    return True;
  }
  else if (VG_STR_CLO(arg, "--mask", argValue))
  {
    if (!parseMask(argValue))
    {
      VG_(printf)("couldn't parse mask file\n");
      VG_(exit)(1);
    }
    inputFilterEnabled = True;
    return True;
  }
  else if (VG_STR_CLO(arg, "--host", argValue))
  {
    Char* dot = VG_(strchr)(argValue, '.');
    *dot = '\0';
    ip1 = (UShort) VG_(strtoll10)(argValue, NULL);
    argValue = dot + 1;
    dot = VG_(strchr)(argValue, '.');
    *dot = '\0';
    ip2 = (UShort) VG_(strtoll10)(argValue, NULL);
    argValue = dot + 1;
    dot = VG_(strchr)(argValue, '.');
    *dot = '\0';
    ip3 = (UShort) VG_(strtoll10)(argValue, NULL);
    argValue = dot + 1;
    ip4 = (UShort) VG_(strtoll10)(argValue, NULL);
    return True;
  }
  else if (VG_STR_CLO(arg, "--file", argValue))
  {
    if (inputfiles == NULL)
    {
      inputfiles = VG_(HT_construct)("inputfiles");
    }
    stringNode* node;
    node = VG_(malloc)("stringNode", sizeof(stringNode));
    node->key = hashCode(argValue);
    node->filename = argValue;
    node->declared = False;
    node->filenum = filenum++;
    VG_(HT_add_node)(inputfiles, node);
    return True;
  }
  else if (VG_STR_CLO(arg, "--check-argv", argValue))
  {
    checkArgvList = VG_(strdup)("checkArgvList", argValue);
    return True;
  }
  else if (VG_STR_CLO(arg, "--host-temp-dir", hostTempDir))
  {
    return True;
  }
  else if (VG_BOOL_CLO(arg, "--check-danger", checkDanger))
  {
    return True;
  }
  else if (VG_STR_CLO(arg, "--dump-file", argValue))
  {
    fdfuncFilter = sr_Res(VG_(open) (argValue, VKI_O_WRONLY | VKI_O_CREAT | VKI_O_TRUNC, PERM_R_W));
    return True;
  }
  else if (VG_BOOL_CLO(arg, "--suppress-subcalls", suppressSubcalls))
  {
    return True;
  }
  else if (VG_BOOL_CLO(arg, "--protect-arg-name", protectArgName))
  {
    return True;
  }
  else if (VG_BOOL_CLO(arg, "--sockets",  sockets))
  {
    return True;
  }
  else if (VG_BOOL_CLO(arg, "--datagrams",  datagrams))
  {
    return True;
  }
  else if (VG_BOOL_CLO(arg, "--replace",  replace))
  {
    return True;
  }
  else if VG_BOOL_CLO(arg, "--check-prediction",  checkPrediction)
  {
    if (depth <= 0)
    {
      checkPrediction = False;
    }
    return True;
  }
  else if VG_BOOL_CLO(arg, "--dump-prediction",  dumpPrediction)
  {
    if (dumpPrediction)
    {
      actual = VG_(malloc)("prediction", (depth + invertdepth) * sizeof(Bool));
    }
    return True;
  }
  else
  {
    return False;
  }
}

static void tg_post_clo_init(void)
{
  Char* predictionFile = concatTempDir("prediction.log");
  Char* replaceFile = concatTempDir("replace_data");
  if (socketfd != 0)
  {
    fdtrace = socketfd;
    fddanger = -socketfd;
    Int size = CHUNK_SIZE;
    VG_(write)(fdtrace, &size, sizeof(Int));
  }
  else if (tempDir == NULL)
  {
    fdtrace = sr_Res(VG_(open)("trace.log", VKI_O_WRONLY | VKI_O_TRUNC | VKI_O_CREAT, PERM_R_W));
    fddanger = sr_Res(VG_(open)("dangertrace.log", VKI_O_WRONLY | VKI_O_TRUNC | VKI_O_CREAT, PERM_R_W));
  }
  else
  {
    Char *traceFile = concatTempDir("trace.log");
    Char *dangerFile = concatTempDir("dangertrace.log");
    fdtrace = sr_Res(VG_(open)(traceFile, VKI_O_WRONLY | VKI_O_TRUNC | VKI_O_CREAT, PERM_R_W));
    fddanger = sr_Res(VG_(open)(dangerFile, VKI_O_WRONLY | VKI_O_TRUNC | VKI_O_CREAT, PERM_R_W));
    VG_(free)(traceFile);
    VG_(free)(dangerFile);
  }
  my_write(fdtrace, "memory_0 : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8);\nregisters_0 : ARRAY BITVECTOR(8) OF BITVECTOR(8);\n", 98);
  my_write(fddanger, "memory_0 : ARRAY BITVECTOR(" PTR_SIZE ") OF BITVECTOR(8);\nregisters_0 : ARRAY BITVECTOR(8) OF BITVECTOR(8);\n", 98);
  /* We need to parse --check-prediction and --replace here since
       we need a directory prefix for opening files */
  if (checkPrediction)
  {
    if (depth > 0)
    {
      SysRes fd = VG_(open)(predictionFile, VKI_O_RDONLY, PERM_R_W);
      prediction = VG_(malloc)("prediction", depth * sizeof(Bool));
      VG_(read)(sr_Res(fd), prediction, depth * sizeof(Bool));
      VG_(close)(sr_Res(fd));
    }
    else
    {
      checkPrediction = False;
    }
  }
  if (replace)
  {
    Int fd = sr_Res(VG_(open)(replaceFile, VKI_O_RDONLY, PERM_R_W));
    VG_(read)(fd, &socketsNum, 4);
    socketsBoundary = socketsNum;
    if (socketsNum > 0)
    {
      replace_data = (replaceData*) VG_(malloc)("replace_data", socketsNum * sizeof(replaceData));
      Int i;
      for (i = 0; i < socketsNum; i++)
      {
        VG_(read)(fd, &(replace_data[i].length), sizeof(Int));
        replace_data[i].data = (Char*) VG_(malloc)("replace_data", replace_data[i].length);
        VG_(read)(fd, replace_data[i].data, replace_data[i].length);
      }
    }
    else
    {
      replace_data = NULL;
    }
    VG_(close)(fd);
  }
  VG_(free)(predictionFile);
  VG_(free)(replaceFile);
 
  /* We need to check argv here to ensure that fdtrace and fddanger 
       were already opened */
  if (checkArgvList != NULL)
  {
    Char* argvFile = concatTempDir("argv.log");
    Int fdargv = sr_Res(VG_(open)(argvFile, VKI_O_WRONLY | VKI_O_TRUNC | VKI_O_CREAT, PERM_R_W));
    Char fileNameBuf[128], traceBuf[256];
    Char* hyphenPos;
    if (hostTempDir != NULL)
    {
      hyphenPos = VG_(strchr)(hostTempDir, '-');
    }
    else
    {
      hyphenPos = VG_(strchr)(tempDir, '-');
    }
#define TEMP_SEGMENT_SIZE 6
    Char tempSegment[TEMP_SEGMENT_SIZE + 1];
    VG_(strncpy)(tempSegment, hyphenPos + 1, TEMP_SEGMENT_SIZE);
    tempSegment[TEMP_SEGMENT_SIZE] = '\0';
    VG_(sprintf)(fileNameBuf, "file__slash_tmp_slash_avalanche_hyphen_%s_slash_argv_dot_log", tempSegment);
    Int l = VG_(sprintf)(traceBuf, "%s : ARRAY BITVECTOR(32) OF BITVECTOR(8);\n", fileNameBuf);
    my_write(fdtrace, traceBuf, l);
    my_write(fddanger, traceBuf, l);
    HChar** argv = VG_(client_argv);
    Int i, j, argvSize = 0;
    Int eqPos;
    Int argc = VG_(sizeXA)(VG_(args_for_client));
    Char* argLengthsFile = concatTempDir("arg_lengths");
    Int fdargl = sr_Res(VG_(open)(argLengthsFile, VKI_O_RDONLY, PERM_R_W));
    Int* argLength = VG_(malloc)("argLength", argc * sizeof(Int));
    for (i = 0; i < argc; i ++)
    {
      VG_(read)(fdargl, &(argLength[i]), sizeof(Int));
    }
    Int *argFilterUnits = VG_(malloc)("argFilterUnits", argc * sizeof(Int));
    for (i = 0; i < argc; i ++)
    {
       argFilterUnits[i] = -1;
    }
    if (!VG_(strcmp)(checkArgvList, "all"))
    {
      for (i = 0; i < argc; i ++)
      {
        argFilterUnits[i] = 1;
      }
    }
    else
    {
      parseArgvMask(checkArgvList, argFilterUnits);
    }
    for (i = 0; i < argc; i ++)
    {
      if (argFilterUnits[i] > 0)
      {
        eqPos = -1;
        if (protectArgName)
        {
          HChar* eqPosC = VG_(strchr)(argv[i], '=');
          if (eqPosC != NULL)
          {
            eqPos = eqPosC - argv[i];
          }
        }
        for (j = 0; j < VG_(strlen)(argv[i]) + 1; j ++)
        {
          if (j > eqPos)
          { 
            taintMemoryFromArgv((HWord) (argv[i] + j), argvSize);
          }
          argvSize ++;
          VG_(write)(fdargv, argv[i] + j, 1);
        }
      }
      else
      {
        for (j = 0; j < VG_(strlen)(argv[i]) + 1; j ++)
        {
          argvSize ++;
          VG_(write)(fdargv, argv[i] + j, 1);
        }
      }
      for (j = VG_(strlen)(argv[i]) + 1; j < argLength[i] + 1; j ++)
      {
        argvSize ++;
        VG_(write)(fdargv, " ", 1);
      }
    }
    VG_(free)(argFilterUnits);
    VG_(free)(argLength);
    VG_(free)(checkArgvList);
    VG_(close)(fdargv);
    VG_(close)(fdargl);
    VG_(free)(argvFile);
    VG_(free)(argLengthsFile);
  }
}

static void tg_print_usage(void)
{
  VG_(printf)(
	"    --startdepth=<number>		the number of conditional jumps after\n"
	"					which the queries for the invertation of\n"
	"					consequent conditional jumps are emitted\n"
	"    --invertdepth=<number>		number of queries to be emitted\n"
	"    --filename=<name>			the name of the file with the input data\n"
	"    --dump-prediction=<yes, no>	indicates whether the file with conditional\n"
	"		 			jumps outcome prediction should be dumped\n"
	"    --check-prediction=<yes, no>	indicates whether the file with\n"
	" 					previously dumped prediction should\n"
	"					be used to check for the occurence\n"
	"					of divergence\n"
        "  special options for sockets:\n"
        "    --sockets=<yes, no>                mark data read from TCP sockets as tainted\n"
        "    --datagrams=<yes, no>              mark data read from UDP sockets as tainted\n"
        "    --host=<IPv4 address>              IP address of the network connection (for TCP sockets only)\n"
        "    --port=<number>                    port number of the network connection (for TCP sockets only)\n"
        "    --replace=<name>                   name of the file with data for replacement\n"
  );
}

static void tg_print_debug_usage(void)
{
  VG_(printf)("");
}

static void tg_pre_clo_init(void)
{
  VG_(details_name)            ("Tracegrind");
  VG_(details_version)         ("1.0");
  VG_(details_description)     ("valgrind IR to STP declarations converter");
  VG_(details_copyright_author)("Copyright (C) iisaev");
  VG_(details_bug_reports_to)  ("iisaev@ispras.ru");
  VG_(basic_tool_funcs)        (tg_post_clo_init,
                                tg_instrument,
                                tg_fini);
  VG_(needs_syscall_wrapper)(pre_call,
			      post_call);
  VG_(track_post_mem_write)(tg_track_post_mem_write);
  VG_(track_new_mem_mmap)(tg_track_mem_mmap);

  VG_(needs_core_errors) ();

  VG_(needs_command_line_options)(tg_process_cmd_line_option,
                                  tg_print_usage,
                                  tg_print_debug_usage);

  taintedMemory = VG_(HT_construct)("taintedMemory");
  taintedRegisters = VG_(HT_construct)("taintedRegisters");
  
  usedOffsets = VG_(newXA) (VG_(malloc), "usedOffsets", VG_(free), sizeof(OSet*));
  inputFiles = VG_(newXA) (VG_(malloc), "inputFiles", VG_(free), sizeof(Char*));
  
  tempSizeTable = VG_(HT_construct)("tempSizeTable");
 
  funcNames = VG_(HT_construct)("funcNames");
  
  diFunctionName = VG_(malloc) ("diFunctionName", 1024 * sizeof(Char));
      
  curdepth = 0;
}

VG_DETERMINE_INTERFACE_VERSION(tg_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
