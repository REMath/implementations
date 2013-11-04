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


#define FZ_DEBUG
#undef FZ_DEBUG


static IRExpr *assignNew(IRSB *bb, IRExpr *e) {
    IRTemp t = newIRTemp(bb->tyenv, Ity_I32);
    switch (typeOfIRExpr(bb->tyenv, e)) {
        case Ity_I1:
            addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_1Uto32, e)));
            break;
        case Ity_I8:
            addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_8Uto32, e)));
            break;
        case Ity_I16:
            addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_16Uto32, e)));
            break;
        case Ity_I32:
            return e;
        case Ity_I64:
            addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_64to32, e)));
            break;
        //case Ity_F64:
        //    addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_F64toI32, e)));
        //    break;
        default:
            VG_(tool_panic)("assignNew");
   }
   return IRExpr_RdTmp(t);
}


#ifdef FZ_DEBUG
static void ppDepReg(Dep *reg) {
    //VG_(printf)("    reg    = %d\n", reg->value.reg);
    VG_(printf)("    size   = %d\n", reg->size);
    VG_(printf)("    constr = %s\n", reg->cons);
}


static void ppDepTmp(Dep *tmp) {
    VG_(printf)("    size   = %d\n", tmp->size);
    VG_(printf)("    constr = %s\n", tmp->cons);
}


static void ppDepAddr(Dep *addr) {
    VG_(printf)("    addr   = 0x%08x\n", (UInt)addr->value.addr);
    VG_(printf)("    size   = %d\n", addr->size);
    VG_(printf)("    constr = %s\n", addr->cons);
}
#else
#define ppDepReg(x)
#define ppDepTmp(x)
#define ppDepAddr(x)
#endif


/*
 * Check that the size of the constraint buffer is large enough to contain the
 * new string. If not, reallocate the buffer.
 */
static void realloc_cons_buf(Dep *d, UInt new_size) {
    d->cons_size *= 2;
    tl_assert(new_size < d->cons_size);
    
    if (d->cons == d->buf) {
        d->cons = VG_(malloc)("fz.rcb.1", d->cons_size);
    }
    else {
        d->cons = VG_(realloc)("fz.rcb.2", d->cons, d->cons_size); 
    }
    
    tl_assert(d->cons != NULL);
}


static void free_cons_buf(Dep *d) {
    if (d->cons != d->buf) {
        VG_(free)(d->cons);
        d->cons = d->buf;
        d->cons_size = XXX_MAX_BUF;
    }
    d->cons[0] = '\x00';
}

#define SPRINTF_CONS(d, fmt, ...) do {                                                 \
    UInt res_snprintf;                                                                 \
    Bool ok = True;                                                                    \
    do {                                                                               \
        res_snprintf = VG_(snprintf)((d).cons, (d).cons_size, (fmt), __VA_ARGS__);     \
        if (res_snprintf >= (d).cons_size - 1) { /* valgrind's buggy snprintf... */    \
            realloc_cons_buf(&(d), res_snprintf);                                      \
            res_snprintf = VG_(snprintf)((d).cons, (d).cons_size, (fmt), __VA_ARGS__); \
            ok = (res_snprintf < (d).cons_size - 1);                                   \
        }                                                                              \
    } while (!ok);                                                                     \
} while (0)


static UInt add_dependency_reg(Reg reg, UInt size) {
    tl_assert(reg >= 0 && reg < MAX_DEP);
    tl_assert(size != 0);
    depreg[reg].size = size;
    
#ifdef FZ_DEBUG
    VG_(printf)("[+] dependency_reg[%d]\n", reg);
#endif
    
    return reg;
}

static UInt add_dependency_tmp(Tmp tmp, UInt size) {
    tl_assert(tmp >= 0 && tmp < MAX_DEP); 
    deptmp[tmp].size = size;

#ifdef FZ_DEBUG
    VG_(printf)("[+] dependency_tmp[%d]\n", tmp);
#endif
    
    return tmp;
}

UInt add_dependency_addr(Addr addr, UInt size) {
    UInt i;
    Dep *depaddr = SELECT_DEPADDR(size);
    UInt *depaddr_number = SELECT_DEPADDR_NUMBER(size);
    
    /* search for an existing dependency and replace it */
    for (i = 0; i < *depaddr_number; i++) {
        if (depaddr[i].value.addr == addr) {
            break;
        }
    }
    
    tl_assert(i < MAX_DEP);
    if (i == *depaddr_number) {
        depaddr[i].value.addr = addr;
        *depaddr_number += 1;
    }
    tl_assert(size != 0);
    depaddr[i].size = size;
    
#ifdef FZ_DEBUG
    VG_(printf)("[+] dependency_addr[%d]\n", i);
#endif
    
    return i;
}

static void del_dependency_tmp(Tmp tmp) {
    tl_assert(tmp >= 0 && tmp < MAX_DEP);
    if (deptmp[tmp].cons[0] != '\x00') {
        free_cons_buf(&deptmp[tmp]);
    }
}

static void del_dependency_reg(Reg reg) {
    tl_assert(reg >= 0 && reg < MAX_DEP);
    if (depreg[reg].cons[0] != '\x00') {
        free_cons_buf(&depreg[reg]);
    }
}

void del_dependency_addr(Addr addr, UInt size) {
    Dep *depaddr = SELECT_DEPADDR(size);
    UInt *depaddr_number = SELECT_DEPADDR_NUMBER(size);
    UInt i, j = *depaddr_number - 1;
    
    for (i = 0; i < *depaddr_number; i++) {
        if (depaddr[i].value.addr == addr) {
#ifdef FZ_DEBUG
            VG_(printf)("[+] removing dependency_addr[%d]\n", i);
            ppDepAddr(&depaddr[i]);
#endif
            free_cons_buf(&depaddr[i]);
            if (i < j) {
                depaddr[i].value.addr = depaddr[j].value.addr;
                depaddr[i].size = depaddr[j].size;
                SPRINTF_CONS(depaddr[i], "%s", depaddr[j].cons);
                free_cons_buf(&depaddr[j]);
            }
            *depaddr_number -= 1; 
            break;
        }
    }
}


static UInt depend_of_reg(Reg reg) {
    tl_assert(reg >= 0 && reg < MAX_DEP);
    return depreg[reg].cons[0] != '\x00';
}

static UInt depend_of_tmp(Tmp tmp) {
    tl_assert(tmp >= 0 && tmp < MAX_DEP);
    return deptmp[tmp].cons[0] != '\x00';
}


/*
 * Write a value to a register
 * tmp is invalid if it's a constant
 */
static VG_REGPARM(0) void helperc_put(Tmp tmp, Reg offset) {
    UInt j;
    
    if (tmp != INVALID_TMP) {
        if (depend_of_tmp(tmp)) {
            j = add_dependency_reg(offset, deptmp[tmp].size);
            SPRINTF_CONS(depreg[j], "PUT(%s)", deptmp[tmp].cons);
            ppDepReg(&depreg[j]);
            return;
        }
    }
    
    /* delete an eventually dependency to the offset if:
     * - the value to write is a constant
     * - or we don't depend of the tmp */ 
    del_dependency_reg(offset);
}


/*
 * Valgrind does implicit size conversion between PUT and GET, so we can't rely
 * on the dependency's size. For example : GET:I32(PUT(1Uto8(a))).
 */
static VG_REGPARM(0) void helperc_get(Reg offset, Tmp tmp, UInt size) {
    UInt j;
    
    if (depend_of_reg(offset)) {
        j = add_dependency_tmp(tmp, size);
        SPRINTF_CONS(deptmp[j], "GET:I%d(%s)", size, depreg[offset].cons);
        ppDepTmp(&deptmp[j]);
        return;
    }
    
    del_dependency_tmp(tmp);
}


static VG_REGPARM(0) void helperc_load(Addr addr, Tmp tmp, Tmp tmp_to, UInt size) {
    UInt a, b, c, i, j, pos;
    
    if (addr != INVALID_ADDR) {
        if (size == 8) {
            for (i = 0; i < depaddr8_number; i++) {
                if (depaddr8[i].value.addr == addr) {
                    if (VG_(strncmp)(depaddr8[i].cons, "input", 5) != 0 && VG_(strncmp)(depaddr8[i].cons, "ST", 2) != 0) {
                        break;
                    }
                    j = add_dependency_tmp(tmp_to, 8);
                    SPRINTF_CONS(deptmp[j], "LDle:I%d(%s)", size, depaddr8[i].cons);
                    ppDepTmp(&deptmp[j]);
                    return;
                }
            }
            
            for (i = 0; i < depaddr16_number; i++) {
                if (addr >= depaddr16[i].value.addr && addr < depaddr16[i].value.addr + 2) {
                    pos = addr - depaddr16[i].value.addr;
                    if (VG_(strncmp)(depaddr16[i].cons, "input", 5) != 0 && VG_(strncmp)(depaddr16[i].cons, "ST", 2) != 0) {
                        break;
                    }
                    j = add_dependency_tmp(tmp_to, 8);
                    SPRINTF_CONS(deptmp[j], "32to8(And32(Shr32(8Uto32(LDle:I8(%s)),0x%x:I32),0xff:I32))", depaddr16[i].cons, 8 * pos);
                    ppDepTmp(&deptmp[j]);
                    return;
                }
            }
            
            for (i = 0; i < depaddr32_number; i++) {
                if (addr >= depaddr32[i].value.addr && addr < depaddr32[i].value.addr + 4) {
                    pos = addr - depaddr32[i].value.addr;
                    if (VG_(strncmp)(depaddr32[i].cons, "input", 5) != 0 && VG_(strncmp)(depaddr32[i].cons, "ST", 2) != 0) {
                        break;
                    }
                    j = add_dependency_tmp(tmp_to, 8);
                    SPRINTF_CONS(deptmp[j], "32to8(And32(Shr32(8Uto32(LDle:I8(%s)),0x%x:I32),0xff:I32))", depaddr32[i].cons, 8 * pos);
                    ppDepTmp(&deptmp[j]);
                    return;
                }
            }
        }
        else if (size == 16) {
            for (i = 0; i < depaddr16_number; i++) {
                if (depaddr16[i].value.addr == addr) {
                    if (VG_(strncmp)(depaddr16[i].cons, "input", 5) != 0 && VG_(strncmp)(depaddr16[i].cons, "ST", 2) != 0) {
                        break;
                    }
                    j = add_dependency_tmp(tmp_to, 16);
                    SPRINTF_CONS(deptmp[j], "LDle:I%d(%s)", size, depaddr16[i].cons);
                    ppDepTmp(&deptmp[j]);
                    return;
                }
            }
            
            for (i = 0; i < depaddr32_number; i++) {
                if (addr >= depaddr32[i].value.addr && addr <= depaddr32[i].value.addr + 2) {
                    pos = addr - depaddr32[i].value.addr;
                    if (VG_(strncmp)(depaddr32[i].cons, "input", 5) != 0 && VG_(strncmp)(depaddr32[i].cons, "ST", 2) != 0) {
                        break;
                    }
                    j = add_dependency_tmp(tmp_to, 16);
                    SPRINTF_CONS(deptmp[j], "32to16(And32(Shr32(16Uto32(LDle:I16(%s)),0x%x:I32),0xffff:I32))", depaddr32[i].cons, 8 * pos);
                    ppDepTmp(&deptmp[j]);
                    return;
                }
            }
        
            for (i = 0; i < depaddr8_number; i++) {
                if (depaddr8[i].value.addr == addr) {
                    for (a = 0; a < depaddr8_number; a++) {
                        if (depaddr8[a].value.addr == addr + 1) {
                            break;
                        }
                    }
                    tl_assert(a != depaddr8_number);
                
                    j = add_dependency_tmp(tmp_to, 16);
                    
                    SPRINTF_CONS(deptmp[j], "Cat16(LDle:I8(%s),LDle:I8(%s))", depaddr8[a].cons, depaddr8[i].cons);
                    ppDepTmp(&deptmp[j]);
                    return;
                }
            }
        }
        else if (size == 32) {
            for (i = 0; i < depaddr32_number; i++) {
                if (depaddr32[i].value.addr == addr) {
                    if (VG_(strncmp)(depaddr32[i].cons, "input", 5) != 0 && VG_(strncmp)(depaddr32[i].cons, "ST", 2) != 0) {
                        break;
                    }
                    j = add_dependency_tmp(tmp_to, 32);
                    SPRINTF_CONS(deptmp[j], "LDle:I32(%s)", depaddr32[i].cons);
                    ppDepTmp(&deptmp[j]);
                    return;
                }
            }
        
            for (i = 0; i < depaddr8_number; i++) {
                if (depaddr8[i].value.addr == addr) {
                    for (a = 0; a < depaddr8_number; a++) {
                        if (depaddr8[a].value.addr == addr + 1) {
                            break;
                        }
                    }
                    for (b = 0; b < depaddr8_number; b++) {
                        if (depaddr8[b].value.addr == addr + 2) {
                            break;
                        }
                    }
                    for (c = 0; c < depaddr8_number; c++) {
                        if (depaddr8[c].value.addr == addr + 3) {
                            break;
                        }
                    }
                    // XXX
                    //tl_assert(a != depaddr8_number && b != depaddr8_number && c != depaddr8_number);
                    if (!(a != depaddr8_number && b != depaddr8_number && c != depaddr8_number)) {
                        continue;
                    }
                
                    j = add_dependency_tmp(tmp_to, 32);
                    SPRINTF_CONS(deptmp[j],
                                 "Cat32(LDle:I8(%s),Cat24(LDle:I8(%s),Cat16(LDle:I8(%s),LDle:I8(%s))))",
                                 depaddr8[c].cons,
                                 depaddr8[b].cons,
                                 depaddr8[a].cons,
                                 depaddr8[i].cons);
                    ppDepTmp(&deptmp[j]);
                    return;
                }
            }
        }
        else if (size == 64) {
            // XXX - currently not supported...
            //VG_(printf)("oops, size = 64\n");
        }
        else {
            VG_(printf)("size = %d\n", size);
            VG_(tool_panic)("helperc_load: invalid size !");
        }
    }
    
    // we can depend either on the temporary number or the temporary value
    // (which is an address)
    if (tmp != INVALID_TMP) {
        if (depend_of_tmp(tmp)) {
            // we don't track pointer: just load previous stored value and input
            if (VG_(strncmp)(deptmp[tmp].cons, "input", 5) != 0 && VG_(strncmp)(deptmp[tmp].cons, "ST", 2) != 0) {
                VG_(printf)("[-] Losing dependency\n");
            }
            else {
                j = add_dependency_tmp(tmp_to, deptmp[tmp].size);
                SPRINTF_CONS(deptmp[j], "LDle:%d(%s)", deptmp[tmp].size, deptmp[tmp].cons);
                ppDepTmp(&deptmp[j]);
                return;
            }
        }
    }
    
    del_dependency_tmp(tmp_to);
}


static VG_REGPARM(0) void helperc_rdtmp(Tmp tmp, Tmp tmp_to) {
    UInt j;
    
    if (tmp != INVALID_TMP) {
        if (depend_of_tmp(tmp)) {
            j = add_dependency_tmp(tmp_to, deptmp[tmp].size);
            SPRINTF_CONS(deptmp[j], "%s", deptmp[tmp].cons);
            ppDepTmp(&deptmp[j]);
            return;
        }
    }
    
    del_dependency_tmp(tmp_to);
}


static VG_REGPARM(0) void helperc_unop(Tmp tmp, Tmp tmp_to, UInt size, UInt op) {
    UInt j;
    char buffer[XXX_MAX_BUF];
    
    if (tmp != INVALID_TMP) {
        if (depend_of_tmp(tmp)) {
            // We must use size, because some expressions change the dependency
            // size. For example: 8Uto32(a).
            j = add_dependency_tmp(tmp_to, size);
            IROp_to_str(op, buffer);
            SPRINTF_CONS(deptmp[j], "%s(%s)", buffer, deptmp[tmp].cons);
            ppDepTmp(&deptmp[j]);
            return;
        }
    }
    
    del_dependency_tmp(tmp_to);
}


static VG_REGPARM(0) void helperc_binop(Tmp tmp1, Tmp tmp2, Tmp tmp_to, UInt op, UInt tmp1_value, UInt tmp2_value, UInt end_size) {
    UInt j1 = 0, j2 = 0;
    Bool b1 = False, b2 = False;
    char *p;
    char buffer[XXX_MAX_BUF];
    char type;
    int size;
    
    if (tmp1 != INVALID_TMP || tmp2 != INVALID_TMP) { 
        if (tmp1 != INVALID_TMP) {
            if (depend_of_tmp(tmp1)) {
                j1 = add_dependency_tmp(tmp_to, end_size);
                b1 = True;
            }
        }
        
        if (tmp2 != INVALID_TMP) {
            if (depend_of_tmp(tmp2)) {
                j2 = add_dependency_tmp(tmp_to, end_size);
                b2 = True;
            }
        }
        
        if (b1 || b2) {
            IROp_to_str(op, buffer);
            type = 'I';
            p = &buffer[VG_(strlen)(buffer) - 1]; // CmpEQ32
            if (*p < '0' || *p > '9') {           // CmpEQ32S
                p--;
            }
            
            switch (op) {
                case Iop_Shl8 ... Iop_Sar64:
                    size = 8;
                    break;
                default:
                    switch (*p) {
                        case '8': size = 8;  break;
                        case '6': size = 16; break;
                        case '2': size = 32; break;
                        case '4': size = 64; break;
                        default:
                            VG_(printf)("buffer = : %s\b", buffer);
                            VG_(tool_panic)("helperc_binop");
                    }
            }
            
            if (b1 && b2) {
                SPRINTF_CONS(deptmp[j2], "%s(%s,%s)", buffer, deptmp[tmp1].cons, deptmp[tmp2].cons);
                ppDepTmp(&deptmp[j2]);
            }
            else if (b1) {
                tmp2_value &= (0xffffffff >> (32 - size));
                SPRINTF_CONS(deptmp[j1], "%s(%s,0x%x:%c%d)", buffer, deptmp[tmp1].cons, tmp2_value, type, size);
                ppDepTmp(&deptmp[j1]);
            }
            else if (b2) {
                tmp1_value &= (0xffffffff >> (32 - size));
                SPRINTF_CONS(deptmp[j2], "%s(0x%x:%c%d,%s)", buffer, tmp1_value, type, size, deptmp[tmp2].cons);
                ppDepTmp(&deptmp[j2]);
            }
            
            return;
        }
    }
    
    del_dependency_tmp(tmp_to);
}


static VG_REGPARM(0) void helperc_mux0x(Tmp cond_tmp, UInt cond_value, Tmp expr0, Tmp exprX, Tmp tmp_to) {
    UInt j;
    Tmp t = (cond_value) ? exprX : expr0;

    // XXX
    /*
    if (depend_of_tmp(cond_tmp)) {
        VG_(printf)("[+] 0x%08x depending of input: if (8to1(%s)) => %d\n", 0x12345678, deptmp[cond_tmp].cons, cond_value);
    }
    */
    
    if (t != INVALID_TMP) {
        if (depend_of_tmp(t)) {
            j = add_dependency_tmp(tmp_to, deptmp[t].size);
            SPRINTF_CONS(deptmp[j], "%s", deptmp[t].cons);
            ppDepTmp(&deptmp[j]);
            return;
        }
    }
    
    del_dependency_tmp(tmp_to);
}


static VG_REGPARM(0) void helperc_store(Addr addr, Tmp tmp) {
    UInt j;
    
    if (tmp != INVALID_TMP) {
        if (depend_of_tmp(tmp)) {
            if (deptmp[tmp].size == 32) {
                // XXX - we're asserting that values don't overlap
                // add dependency to the 32 bit value
                j = add_dependency_addr(addr, 32);
                SPRINTF_CONS(depaddr32[j], "STle(%s)", deptmp[tmp].cons);
                ppDepAddr(&depaddr32[j]);
                
                // delete any dependency stored at this address
                for (j = 0; j < depaddr16_number; j++) {
                    if (depaddr16[j].value.addr >= addr && depaddr16[j].value.addr <= addr + 2) {
                        del_dependency_addr(depaddr16[j].value.addr, 16);
                    }
                }
                
                for (j = 0; j < depaddr8_number; j++) {
                    if (depaddr8[j].value.addr >= addr && depaddr8[j].value.addr < addr + 4) {
                        del_dependency_addr(depaddr8[j].value.addr, 8);
                    }
                }
            }
            else if (deptmp[tmp].size == 16) {
                j = add_dependency_addr(addr, 16);
                SPRINTF_CONS(depaddr16[j], "STle(%s)", deptmp[tmp].cons);
                ppDepAddr(&depaddr16[j]);
                
                for (j = 0; j < depaddr8_number; j++) {
                    if (depaddr8[j].value.addr >= addr && depaddr8[j].value.addr < addr + 2) {
                        del_dependency_addr(depaddr8[j].value.addr, 8);
                    }
                }
            }
            else if (deptmp[tmp].size == 8) {
                // add dependency to the 8 bit value
                j = add_dependency_addr(addr, 8);
                SPRINTF_CONS(depaddr8[j], "STle(%s)", deptmp[tmp].cons);
                ppDepAddr(&depaddr8[j]);
                
                // if it overwrite a 32 or 16 bits value, fragment them
            }
            else {
                VG_(printf)("deptmp[%d].size = %d\n", tmp, deptmp[tmp].size);
                VG_(printf)("deptmp[%d].cons = %s", tmp, deptmp[tmp].cons);
                VG_(tool_panic)("helperc_store: dependency size not handled");
            }
            return;
        }
    }
    
    // XXX !
    del_dependency_addr(addr, 32);
    del_dependency_addr(addr, 16);
    del_dependency_addr(addr, 8);
}


static VG_REGPARM(0) void helperc_exit(Tmp guard, Addr addr, UInt taken) {
    if (depend_of_tmp(guard)) {
        VG_(printf)("[+] 0x%08x depending of input: if (%s) => %d\n", (UInt)addr, deptmp[guard].cons, taken);
        return;
    }
}


static VG_REGPARM(0) void helperc_x86g_calculate_condition(Tmp tmp_to, UInt cond, UInt cc_op, Tmp cc_dep1, Tmp cc_dep2,
                                                           UInt cc_dep1_value, UInt cc_dep2_value) {
    UInt j1 = 0, j2 = 0;
    Bool b1 = False, b2 = False;
    char type = 'I';
    int size = 32;
    
    if (depend_of_tmp(cc_dep1)) {
        j1 = add_dependency_tmp(tmp_to, deptmp[cc_dep1].size);
        b1 = True;
    }

    if (depend_of_tmp(cc_dep2)) {
        j2 = add_dependency_tmp(tmp_to, deptmp[cc_dep2].size);
        b2 = True;
    }
    
    if (b1 || b2) {        
        if (b1 && b2) {
            SPRINTF_CONS(deptmp[j2], "x86g_calculate_condition(0x%x:I32,0x%x:I32,%s,%s)", cond, cc_op, deptmp[cc_dep1].cons, deptmp[cc_dep2].cons);
            ppDepTmp(&deptmp[j2]);
        }
        else if (b1) {
            SPRINTF_CONS(deptmp[j1], "x86g_calculate_condition(0x%x:I32,0x%x:I32,%s,0x%x:%c%d)", cond, cc_op, deptmp[cc_dep1].cons, cc_dep2_value, type, size);
            ppDepTmp(&deptmp[j1]);
        }
        else if (b2) {
            SPRINTF_CONS(deptmp[j2], "x86g_calculate_condition(0x%x:I32,0x%x:I32,0x%x:%c%d,%s)", cond, cc_op, cc_dep1_value, type, size, deptmp[cc_dep2].cons);
            ppDepTmp(&deptmp[j2]);
        }
        
        return;
    } 
        
    del_dependency_tmp(tmp_to);
}


IRSB* fz_instrument ( VgCallbackClosure* closure,
                      IRSB* bb_in,
                      VexGuestLayout* layout, 
                      VexGuestExtents* vge,
                      IRType gWordTy, IRType hWordTy )
{
    Addr current_addr = 0;
    IRSB*   bb;
    Int     i, j;
    
    if (gWordTy != hWordTy) {
      /* We don't currently support this case. */
      VG_(tool_panic)("host/guest word size mismatch");
    }

    /* Set up SB */
    bb = deepCopyIRSBExceptStmts(bb_in);

    // Copy verbatim any IR preamble preceding the first IMark
    i = 0;
    while (i < bb_in->stmts_used && bb_in->stmts[i]->tag != Ist_IMark) {
        addStmtToIRSB(bb, bb_in->stmts[i]);
        i++;
    }
    
    // Iterate over the remaining stmts to generate instrumentation.
    tl_assert(bb_in->stmts_used > 0);
    tl_assert(i >= 0);
    tl_assert(i < bb_in->stmts_used);
    tl_assert(bb_in->stmts[i]->tag == Ist_IMark);
    
    for (/*use current i*/; i < bb_in->stmts_used; i++) {
        IRStmt* st = bb_in->stmts[i];
        IRExpr *addr, *data, **args, *arg, *e1, *e2;
        IRTemp to = 0; /* gcc warning */
        IRDirty *di;
        UInt size = 0;
        
        if (!st || st->tag == Ist_NoOp) {
            continue;
        }
        
        if (FZ_(verbose)) {
            VG_(printf)("->");
            ppIRStmt(st);
            VG_(printf)("\n\n");
        }

        switch (st->tag) {
            case Ist_IMark:
                current_addr = st->Ist.IMark.addr;
                break;
        
            case Ist_Put:
                tl_assert(isIRAtom(st->Ist.Put.data));
                if (st->Ist.Put.data->tag == Iex_RdTmp) {
                    add_dirty2(helperc_put,
                               mkIRExpr_HWord(st->Ist.Put.data->Iex.RdTmp.tmp),
                               mkIRExpr_HWord(st->Ist.Put.offset));
                }
                else {
                    add_dirty2(helperc_put,
                               mkIRExpr_HWord(INVALID_TMP),
                               mkIRExpr_HWord(st->Ist.Put.offset));
                }
                break;
                
            case Ist_WrTmp:
                switch (st->Ist.WrTmp.data->tag) {
                    case Iex_Const:
                        to = st->Ist.WrTmp.tmp;
                        add_dirty2(helperc_rdtmp,
                                   mkIRExpr_HWord(INVALID_TMP),
                                   mkIRExpr_HWord(to));
                        break;
                        
                    case Iex_RdTmp:
                        to = st->Ist.WrTmp.tmp;
                        add_dirty2(helperc_rdtmp,
                                   mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.RdTmp.tmp),
                                   mkIRExpr_HWord(to));
                        break;
                        
                    case Iex_Load:
                        addr = st->Ist.WrTmp.data->Iex.Load.addr;
                        to = st->Ist.WrTmp.tmp;
                        
                        tl_assert(isIRAtom(addr));
                        
                        j = st->Ist.WrTmp.data->Iex.Load.ty;
                        size = (j != Ity_I1) ? sizeofIRType(j) * 8 : 1;
                        
                        if (addr->tag == Iex_Const) {
                            add_dirty4(helperc_load,
                                       mkIRExpr_HWord(addr->Iex.Const.con->Ico.U32),
                                       mkIRExpr_HWord(INVALID_TMP),
                                       mkIRExpr_HWord(to),
                                       mkIRExpr_HWord(size));
                        }
                        else if (addr->tag == Iex_RdTmp) {
                            add_dirty4(helperc_load,
                                       addr,
                                       mkIRExpr_HWord(addr->Iex.RdTmp.tmp),
                                       mkIRExpr_HWord(to),
                                       mkIRExpr_HWord(size));
                        }
                        break;
                        
                    case Iex_Get:
                        j = st->Ist.WrTmp.data->Iex.Get.ty;
                        size = (j != Ity_I1) ? sizeofIRType(j) * 8 : 1;
                        add_dirty3(helperc_get,
                                   mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Get.offset),
                                   mkIRExpr_HWord(st->Ist.WrTmp.tmp),
                                   mkIRExpr_HWord(size));
                        break;
                        
                    case Iex_Unop:
                        arg = st->Ist.WrTmp.data->Iex.Unop.arg;
                        to = st->Ist.WrTmp.tmp;
                        
                        tl_assert(isIRAtom(arg));
                        
                        if (arg->tag == Iex_RdTmp) {
                            size = (bb->tyenv->types[to] != Ity_I1) ? sizeofIRType(bb->tyenv->types[to]) * 8 : 1;
                            add_dirty4(helperc_unop,
                                       mkIRExpr_HWord(arg->Iex.RdTmp.tmp),
                                       mkIRExpr_HWord(to),
                                       mkIRExpr_HWord(size),
                                       mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Unop.op));
                        }
                        else {
                            add_dirty4(helperc_unop,
                                       mkIRExpr_HWord(INVALID_TMP),
                                       mkIRExpr_HWord(to),
                                       mkIRExpr_HWord(size),
                                       mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Unop.op));
                        
                        }
                        break;
                        
                    case Iex_Binop:
                        j = 0;
                        switch (st->Ist.WrTmp.data->Iex.Binop.op) {
                            case Iop_AddF64 ... Iop_CalcFPRF:
                                j = 1;
                                break;
                            default:
                                break;
                        }
                         
                        e1 = st->Ist.WrTmp.data->Iex.Binop.arg1;
                        e2 = st->Ist.WrTmp.data->Iex.Binop.arg2;
                        
                        tl_assert(isIRAtom(e1));
                        tl_assert(isIRAtom(e2));
                        
                        size = (bb->tyenv->types[st->Ist.WrTmp.tmp] != Ity_I1) ? sizeofIRType(bb->tyenv->types[st->Ist.WrTmp.tmp]) * 8 : 1;
                        
                        // this is a floating point operation, we don't care about it
                        // remove the dependency to the destination register
                        if (j == 1) {
                            add_dirty7(helperc_binop,
                                       mkIRExpr_HWord(INVALID_TMP),
                                       mkIRExpr_HWord(INVALID_TMP),
                                       mkIRExpr_HWord(st->Ist.WrTmp.tmp),
                                       mkIRExpr_HWord(0),
                                       mkIRExpr_HWord(0),
                                       mkIRExpr_HWord(0),
                                       mkIRExpr_HWord(0));
                            break;
                        }
                        
                        add_dirty7(helperc_binop,
                                   mkIRExpr_HWord((e1->tag == Iex_RdTmp) ? e1->Iex.RdTmp.tmp : INVALID_TMP),
                                   mkIRExpr_HWord((e2->tag == Iex_RdTmp) ? e2->Iex.RdTmp.tmp : INVALID_TMP),
                                   mkIRExpr_HWord(st->Ist.WrTmp.tmp),
                                   mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Binop.op),
                                   (e1->tag == Iex_RdTmp) ? assignNew(bb, e1) : mkIRExpr_HWord(e1->Iex.Const.con->Ico.U32),
                                   (e2->tag == Iex_RdTmp) ? assignNew(bb, e2) : mkIRExpr_HWord(e2->Iex.Const.con->Ico.U32),
                                   mkIRExpr_HWord(size));
                        break;
                        
                    case Iex_Mux0X:
                        e1 = st->Ist.WrTmp.data->Iex.Mux0X.expr0;
                        e2 = st->Ist.WrTmp.data->Iex.Mux0X.exprX;
                        
                        tl_assert(st->Ist.WrTmp.data->Iex.Mux0X.cond->tag == Iex_RdTmp);
                        tl_assert(isIRAtom(e1));
                        tl_assert(isIRAtom(e2));
                        
                        add_dirty5(helperc_mux0x,
                                   mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Mux0X.cond->Iex.RdTmp.tmp),
                                   assignNew(bb, st->Ist.WrTmp.data->Iex.Mux0X.cond),
                                   mkIRExpr_HWord((e1->tag == Iex_RdTmp) ? e1->Iex.RdTmp.tmp : INVALID_TMP),
                                   mkIRExpr_HWord((e2->tag == Iex_RdTmp) ? e2->Iex.RdTmp.tmp : INVALID_TMP),
                                   mkIRExpr_HWord(st->Ist.WrTmp.tmp));
                        
                        break;
                        
                    case Iex_Triop: // only used by floating point operations
                        break;
                        
                    case Iex_GetI:  // only used by floating point operations
                        break;
                        
                    case Iex_CCall:
                        // XXX - x86g_calculate_condition
                        // look at guest_x86_spechelper
                        // encounterd when IR optimization failed
                        if (VG_(strcmp)(st->Ist.WrTmp.data->Iex.CCall.cee->name, "x86g_calculate_condition") == 0) {
                            args = st->Ist.WrTmp.data->Iex.CCall.args;
                            tl_assert(args[0]->tag == Iex_Const && args[0]->Iex.Const.con->tag == Ico_U32);
                            //tl_assert(args[1]->tag == Iex_RdTmp);
                            if (args[1]->tag == Iex_RdTmp) {
                                tl_assert(args[2]->tag == Iex_RdTmp);
                                tl_assert(args[3]->tag == Iex_RdTmp);
                                tl_assert(args[4]->tag == Iex_RdTmp);
                                
                                add_dirty7(helperc_x86g_calculate_condition,
                                           mkIRExpr_HWord(st->Ist.WrTmp.tmp),               // to
                                           mkIRExpr_HWord(args[0]->Iex.Const.con->Ico.U32), // cond
                                           args[1],                                         // cc_op
                                           mkIRExpr_HWord(args[2]->Iex.RdTmp.tmp),          // cc_dep1
                                           mkIRExpr_HWord(args[3]->Iex.RdTmp.tmp),          // cc_dep2
                                           args[2],                                         // cc_dep1
                                           args[3]);                                        // cc_dep2
                            }
                            else {
                                VG_(printf)("oops, we depend of x86g_calculate_condition: %d, %d\n", args[0]->Iex.Const.con->Ico.U32, args[1]->Iex.Const.con->Ico.U32);
                                //VG_(tool_panic)("");
                                // just remove the dependency
                                add_dirty2(helperc_rdtmp,
                                           mkIRExpr_HWord(INVALID_TMP),
                                           mkIRExpr_HWord(st->Ist.WrTmp.tmp));
                            }
                        }
                        else {
                            // just remove the dependency
                            add_dirty2(helperc_rdtmp,
                                       mkIRExpr_HWord(INVALID_TMP),
                                       mkIRExpr_HWord(st->Ist.WrTmp.tmp));
                        }
                        break;
                        
                    //case Iex_Binder:
                    //    break;
                        
                    //case Iex_Qop:
                    //    break;
                        
                    default:
                        ppIRStmt(st);
                        VG_(tool_panic)("Ist_WrTmp: data->tag not handled");
                        break;
                }
                break;
                
            case Ist_Store:
                data = st->Ist.Store.data;
                tl_assert(isIRAtom(data));
                tl_assert(isIRAtom(st->Ist.Store.addr));
                
                if (data->tag == Iex_RdTmp) {
                    j = bb->tyenv->types[data->Iex.RdTmp.tmp];
                    size = (j != Ity_I1) ? sizeofIRType(j) * 8 : 1;
                }
                else { // data->tag == Iex_Const
                    j = typeOfIRConst(data->Iex.Const.con);
                    size = (j != Ity_I1) ? sizeofIRType(j) * 8 : 1;
                }
                
                add_dirty2(helperc_store,
                           (st->Ist.Store.addr->tag == Iex_Const) ? mkIRExpr_HWord(st->Ist.Store.addr->Iex.Const.con->Ico.U32) : st->Ist.Store.addr,
                           mkIRExpr_HWord((data->tag == Iex_RdTmp) ? data->Iex.RdTmp.tmp : INVALID_TMP));
                break;
                
            case Ist_Exit:
                tl_assert(st->Ist.Exit.guard->tag == Iex_RdTmp);
                add_dirty3(helperc_exit,
                           mkIRExpr_HWord(st->Ist.Exit.guard->Iex.RdTmp.tmp),
                           mkIRExpr_HWord(current_addr),
                           assignNew(bb, st->Ist.Exit.guard));
                break;
                
            case Ist_PutI:
                //VG_(printf)("oops, tag Ist_PutI not handled at 0x%08x\n", current_addr);
                break;
            case Ist_NoOp:
            case Ist_AbiHint:
            case Ist_MBE:
            case Ist_Dirty:
            default:
                break;
        }
        
        /* must be after the switch, otherwise Ist_Exit can jump causing helper
           not to be called */
        addStmtToIRSB(bb, st);
    }
   
    return bb;
}
