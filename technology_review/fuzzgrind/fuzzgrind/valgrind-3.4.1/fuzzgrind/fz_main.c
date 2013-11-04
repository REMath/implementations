/*  This file is part of Fuzzgrind.
 *  Copyright (C) 2009 Gabriel Campana
 *  
 *  Based heavily on Flayer by redpig@dataspill.org
 *  Copyright (C) 2006,2007 Will Drewry <redpig@dataspill.org>
 *  Some portions copyright (C) 2007 Google Inc.
 * 
 *  Based heavily on MemCheck by jseward@acm.org
 *  MemCheck: Copyright (C) 2000-2007 Julian Seward
 *  jseward@acm.org
 * 
 * 
 *  This program is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License as
 *  published by the Free Software Foundation; either version 2 of the
 *  License, or (at your option) any later version.
 *  
 *  This program is distributed in the hope that it will be useful, but
 *  WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  General Public License for more details.
 *  
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
 *  02111-1307, USA.
 *  
 *  The GNU General Public License is contained in the file LICENCE.
 */


#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_options.h"
#include "pub_tool_machine.h"
#include "pub_tool_vkiscnums.h"
#include "pub_tool_mallocfree.h"
#include "fz.h"


Dep deptmp[MAX_DEP];
Dep depreg[MAX_DEP];
Dep depaddr8[MAX_DEP];
Dep depaddr16[MAX_DEP];
Dep depaddr32[MAX_DEP];
UInt depaddr8_number = 0;
UInt depaddr16_number = 0;
UInt depaddr32_number = 0;


#define FZ_DEBUG
//#undef FZ_DEBUG


static void fz_fini(Int exitcode)
{
}


static void fz_post_clo_init(void) {
    FZ_(setup_tainted_map)();
}

 /*------------------------------------------------------------*/
/*--- Syscall event handlers                                ---*/
/*------------------------------------------------------------*/



static void fz_pre_syscall(ThreadId tid, UInt syscallno) {
}


static void fz_post_syscall(ThreadId tid, UInt syscallno, SysRes res) {
    switch (syscallno) {
        case __NR_read:
            FZ_(syscall_read)(tid, res);
            break;
        case __NR_open:
            FZ_(syscall_open)(tid, res);
            break;
        case __NR_close:
            FZ_(syscall_close)(tid, res);
            break;
        case __NR_lseek:
#ifdef __NR__llseek
        case __NR__llseek:
#endif
            FZ_(syscall_lseek)(tid, res);
            break;
#ifdef __NR_mmap
        case __NR_mmap:
#endif
#ifdef __NR_mmap2
        case __NR_mmap2:
#endif
            FZ_(syscall_mmap2)(tid, res);
            break;
        case __NR_munmap:
            FZ_(syscall_munmap)(tid, res);
            break;
        default:
            break;
    }
}

/*------------------------------------------------------------*/
/*--- Command line args                                    ---*/
/*------------------------------------------------------------*/

static Char   FZ_(default_file_filter)[]      = "";
Char*         FZ_(clo_file_filter)            = FZ_(default_file_filter);
Bool          FZ_(clo_taint_file)             = False;
Bool          FZ_(clo_taint_stdin)            = False;
Bool          FZ_(verbose)                    = False;

static Bool fz_process_cmd_line_options(Char* arg) {
    VG_STR_CLO(arg, "--file-filter", FZ_(clo_file_filter))
    else VG_BOOL_CLO(arg, "--taint-stdin", FZ_(clo_taint_stdin))
    else VG_BOOL_CLO(arg, "--taint-file", FZ_(clo_taint_file))
    //else VG_BOOL_CLO(arg, "--taint-network", FL_(clo_taint_network))
    else VG_BOOL_CLO(arg, "--show-ir", FZ_(verbose))
    
    return True;
}

static void fz_print_usage(void) {  
   VG_(printf)(

"    --taint-stdin=no|yes             enables stdin tainting [no]\n"
"    --taint-file=no|yes              enables file tainting [no]\n"
//"    --taint-network=no|yes           enables network tainting [no]\n"
"    --file-filter=/path/prefix       enforces tainting on any files under\n"
"                                     the given prefix. []\n"
"    --show-ir=no|yes                 show intermediate representation statements [no]\n"
   );
}

static void fz_print_debug_usage(void) {  
}


static void fz_pre_clo_init(void)
{
    UInt i;
    VG_(details_name)            ("Fuzzgrind");
    VG_(details_version)         (NULL);
    VG_(details_description)     ("a super fuzzer");
    VG_(details_copyright_author)(
      "Copyright (C) 2008-2009, by Gabriel Campana.");
    VG_(details_bug_reports_to)  (VG_BUGS_TO);

    VG_(basic_tool_funcs)        (fz_post_clo_init,
                                  fz_instrument,
                                  fz_fini);

    VG_(needs_command_line_options)(fz_process_cmd_line_options,
                                    fz_print_usage,
                                    fz_print_debug_usage);
    
    VG_(needs_syscall_wrapper)   ( fz_pre_syscall,
                                   fz_post_syscall );
    
    VG_(memset)(deptmp, 0, sizeof(deptmp));
    VG_(memset)(depreg, 0, sizeof(deptmp));
    VG_(memset)(depaddr8, 0, sizeof(depaddr8));
    VG_(memset)(depaddr16, 0, sizeof(depaddr16));
    VG_(memset)(depaddr32, 0, sizeof(depaddr32));
    
    for (i = 0; i < MAX_DEP; i++) {
        deptmp[i].cons = deptmp[i].buf;
        deptmp[i].cons[0] = '\x00';
        depreg[i].cons = depreg[i].buf;
        depreg[i].cons[0] = '\x00';
        depaddr8[i].cons = depaddr8[i].buf;
        depaddr16[i].cons = depaddr16[i].buf;
        depaddr32[i].cons = depaddr32[i].buf;
        deptmp[i].cons_size = XXX_MAX_BUF;
        depreg[i].cons_size = XXX_MAX_BUF;
        depaddr8[i].cons_size = XXX_MAX_BUF;
        depaddr16[i].cons_size = XXX_MAX_BUF;
        depaddr32[i].cons_size = XXX_MAX_BUF;
    }
}

VG_DETERMINE_INTERFACE_VERSION(fz_pre_clo_init)
