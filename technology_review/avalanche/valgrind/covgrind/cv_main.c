/*--------------------------------------------------------------------------------*/
/*-------------------------------- AVALANCHE -------------------------------------*/
/*-------- Covgrind. Dumps IR basic blocks addresses to file.   cv_main.c --------*/
/*--------------------------------------------------------------------------------*/

/*
   This file is part of Covgrind, the Valgrind tool,
   which dumps addresses of all executed basic blocks
   in Valgrind IR

   Copyright (C) 2009-2011 Ildar Isaev
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

#include "pub_tool_basics.h"
#include "pub_tool_options.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_hashtable.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_vki.h"
#include "pub_tool_vkiscnums.h"
#include "pub_tool_libcbase.h"

#include <avalanche.h>

#define PERM_R_W VKI_S_IRUSR | VKI_S_IROTH | VKI_S_IRGRP | \
                 VKI_S_IWUSR | VKI_S_IWOTH | VKI_S_IWGRP

VgHashTable basicBlocksTable;

UInt alarm = 0;

extern Bool isKernelSignal;
extern Bool isSelfSignal;

extern UShort port;
extern Bool sockets;
extern Bool datagrams;
extern UChar ip1, ip2, ip3, ip4;
extern Int cursocket;
extern ULong curoffs;

Bool replace = False;
Bool isRead = False;
Bool noCoverage = False;
extern Bool isRecv;

static Int socketsNum = 0;
static Int socketsBoundary;
static replaceData* replace_data;
static Char* bbFileName = NULL;
static Char* tempDir;
static Char* replaceFileName;

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


void pre_call(ThreadId tid, UInt syscallno)
{
  if (syscallno == __NR_read)
  {
    isRead = True;
  }
}

void post_call(ThreadId tid, UInt syscallno, SysRes res)
{
  if (syscallno == __NR_read)
  {
    isRead = False;
  }
  else if ((syscallno == __NR_clone) && !sr_isError(res) && (sr_Res(res) == 0))
  {
    //VG_(printf)("__NR_clone\n");
    //VG_(exit)(0);
  }
}

static
IRSB* cv_instrument ( VgCallbackClosure* closure,
                      IRSB* sbIn,
                      VexGuestLayout* layout, 
                      VexGuestExtents* vge,
                      IRType gWordTy, IRType hWordTy )
{      
  if (!noCoverage)
  {
    bbNode* n = (bbNode*) VG_(malloc)("bbNode", sizeof(bbNode)); 
    n->key = vge->base[0]; 
    VG_(HT_add_node)(basicBlocksTable, n);
  }
  return sbIn;
}


static void cv_fini(Int exitcode)
{
  if (!noCoverage)
  {
    VG_(HT_ResetIter)(basicBlocksTable);
    bbNode* n = (bbNode*) VG_(HT_Next)(basicBlocksTable);
    SysRes fd;
    Char *bbFile;
    if (bbFileName != NULL)
    {
      bbFile = concatTempDir(bbFileName);
    }
    else
    {
      bbFile = concatTempDir("basic_blocks.log");
    }
    fd = VG_(open)(bbFile, VKI_O_WRONLY | VKI_O_TRUNC | VKI_O_CREAT, PERM_R_W);
    if (!sr_isError(fd))
    {
      while (n != NULL)
      {
        UWord addr = n->key;
        VG_(write)(sr_Res(fd), &addr, sizeof(addr));
        n = (bbNode*) VG_(HT_Next)(basicBlocksTable);
      }
      VG_(close)(sr_Res(fd));
    }
    VG_(free)(bbFile);
  }
  if (isKernelSignal)
  {
    VG_(printf)("Terminated by kernel signal\n");
  }
  if (isSelfSignal)
  {
    VG_(printf)("Terminated by self-sent signal\n");
  }
}

static Bool cv_process_cmd_line_option(Char* arg) 
{ 
  Char* addr;
  if (VG_INT_CLO(arg, "--alarm", alarm))
  { 
    return True;
  }
  else if (VG_STR_CLO(arg, "--filename", bbFileName))
  {
    return True;
  }
  else if (VG_STR_CLO(arg, "--port", addr))
  {
    port = (UShort) VG_(strtoll10)(addr, NULL);
    return True;
  }
  else if (VG_BOOL_CLO(arg, "--sockets", sockets))
  { 
    return True; 
  }
  else if (VG_BOOL_CLO(arg, "--datagrams", datagrams))
  { 
    return True; 
  }
  else if (VG_BOOL_CLO(arg, "--no-coverage", noCoverage))
  { 
    return True; 
  }
  else if (VG_STR_CLO(arg, "--replace",  replaceFileName))
  { 
    replace = True;
    return True; 
  }
  else if (VG_STR_CLO(arg, "--temp-dir", tempDir))
  {
    return True;
  }
  else if (VG_STR_CLO(arg, "--host", addr))
  {
    Char* dot = VG_(strchr)(addr, '.');
    *dot = '\0';
    ip1 = (UShort) VG_(strtoll10)(addr, NULL);
    addr = dot + 1;
    dot = VG_(strchr)(addr, '.');
    *dot = '\0';
    ip2 = (UShort) VG_(strtoll10)(addr, NULL);
    addr = dot + 1;
    dot = VG_(strchr)(addr, '.');
    *dot = '\0';
    ip3 = (UShort) VG_(strtoll10)(addr, NULL);
    addr = dot + 1;
    ip4 = (UShort) VG_(strtoll10)(addr, NULL);
    return True;
  }
  else
  {
    return False;
  }
} 

static void cv_post_clo_init()
{
  if (alarm != 0)
  {
    VG_(alarm)(alarm);
  }
  if (replace)
  {
    Char* replaceFile = concatTempDir(replaceFileName);
    Int fd = sr_Res(VG_(open)(replaceFile, VKI_O_RDWR, PERM_R_W));
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
    VG_(free)(replaceFile);
  }
}

static void cv_print_usage() 
{   
  VG_(printf)( 
	"    --alarm=<number>		the maximum time for a program run"
        "  special options for sockets:\n"
        "    --sockets=<yes, no>        mark data read from TCP sockets as tainted\n"
        "    --datagrams=<yes, no>      mark data read from UDP sockets as tainted\n"
        "    --host=<IPv4 address>      IP address of the network connection (for TCP sockets only)\n"
        "    --port=<number>            port number of the network connection (for TCP sockets only)\n"
        "    --replace=<name>           name of the file with data for replacement\n"
        "    --no-coverage=<yes, no>    do not dump list of covered basic blocks (for exploit reproduction)\n"
  ); 
} 

static void cv_print_debug_usage() 
{   
  VG_(printf)(""); 
} 

void cv_track_post_mem_write(CorePart part, ThreadId tid, Addr a, SizeT size)
{
  Addr index; 
  if ((isRead || isRecv) && (sockets || datagrams) && (cursocket != -1))
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
      }
    }
  }
}

static void cv_pre_clo_init(void)
{
  VG_(details_name)            ("Covgrind");
  VG_(details_version)         ("1.0");
  VG_(details_description)     ("IR basic blocks addresses dumper");
  VG_(details_copyright_author)("Copyright (C) iisaev");
  VG_(details_bug_reports_to)  ("iisaev@ispras.ru");

   VG_(basic_tool_funcs)        (cv_post_clo_init,
                                 cv_instrument,
                                 cv_fini);

   VG_(needs_command_line_options)(cv_process_cmd_line_option,
                                   cv_print_usage,
                                   cv_print_debug_usage);
  VG_(track_post_mem_write)(cv_track_post_mem_write);
  VG_(needs_syscall_wrapper)(pre_call,
			     post_call);
  basicBlocksTable = VG_(HT_construct)("basicBlocksTable");

  /* No needs, no core events to track */
}

VG_DETERMINE_INTERFACE_VERSION(cv_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
