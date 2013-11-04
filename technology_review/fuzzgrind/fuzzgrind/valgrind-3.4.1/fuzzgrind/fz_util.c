/*  This file is part of Fuzzgrind.
 *  Copyright (C) 2009 Gabriel Campana
 * 
 *  Based heavily on LibVEX by OpenWorks LLP
 *  LibVEX: Copyright (C) 2004-2008 OpenWorks LLP.
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


/* borrowed from priv/ir/irdefs.c: ppIROp() */
void IROp_to_str(IROp op, Char *buffer) {
    HChar* str; 
    IROp    base;
    switch (op) {
        case Iop_Add8 ... Iop_Add64:
            str = "Add"; base = Iop_Add8; break;
        case Iop_Sub8 ... Iop_Sub64:
            str = "Sub"; base = Iop_Sub8; break;
        case Iop_Mul8 ... Iop_Mul64:
            str = "Mul"; base = Iop_Mul8; break;
        case Iop_Or8 ... Iop_Or64:
            str = "Or"; base = Iop_Or8; break;
        case Iop_And8 ... Iop_And64:
            str = "And"; base = Iop_And8; break;
        case Iop_Xor8 ... Iop_Xor64:
            str = "Xor"; base = Iop_Xor8; break;
        case Iop_Shl8 ... Iop_Shl64:
            str = "Shl"; base = Iop_Shl8; break;
        case Iop_Shr8 ... Iop_Shr64:
            str = "Shr"; base = Iop_Shr8; break;
        case Iop_Sar8 ... Iop_Sar64:
            str = "Sar"; base = Iop_Sar8; break;
        case Iop_CmpEQ8 ... Iop_CmpEQ64:
            str = "CmpEQ"; base = Iop_CmpEQ8; break;
        case Iop_CmpNE8 ... Iop_CmpNE64:
            str = "CmpNE"; base = Iop_CmpNE8; break;
        case Iop_Not8 ... Iop_Not64:
            str = "Not"; base = Iop_Not8; break;
        /* other cases must explicitly "return;" */
        case Iop_8Uto16:    VG_(strcpy)(buffer, "8Uto16");  return;
        case Iop_8Uto32:    VG_(strcpy)(buffer, "8Uto32");  return;
        case Iop_16Uto32:  VG_(strcpy)(buffer, "16Uto32"); return;
        case Iop_8Sto16:    VG_(strcpy)(buffer, "8Sto16");  return;
        case Iop_8Sto32:    VG_(strcpy)(buffer, "8Sto32");  return;
        case Iop_16Sto32:  VG_(strcpy)(buffer, "16Sto32"); return;
        case Iop_32Sto64:  VG_(strcpy)(buffer, "32Sto64"); return;
        case Iop_32Uto64:  VG_(strcpy)(buffer, "32Uto64"); return;
        case Iop_32to8:     VG_(strcpy)(buffer, "32to8");    return;
        case Iop_16Uto64:  VG_(strcpy)(buffer, "16Uto64"); return;
        case Iop_16Sto64:  VG_(strcpy)(buffer, "16Sto64"); return;
        case Iop_8Uto64:    VG_(strcpy)(buffer, "8Uto64"); return;
        case Iop_8Sto64:    VG_(strcpy)(buffer, "8Sto64"); return;
        case Iop_64to16:    VG_(strcpy)(buffer, "64to16"); return;
        case Iop_64to8:     VG_(strcpy)(buffer, "64to8");  return;

        case Iop_Not1:      VG_(strcpy)(buffer, "Not1");     return;
        case Iop_32to1:     VG_(strcpy)(buffer, "32to1");    return;
        case Iop_64to1:     VG_(strcpy)(buffer, "64to1");    return;
        case Iop_1Uto8:     VG_(strcpy)(buffer, "1Uto8");    return;
        case Iop_1Uto32:    VG_(strcpy)(buffer, "1Uto32");  return;
        case Iop_1Uto64:    VG_(strcpy)(buffer, "1Uto64");  return;
        case Iop_1Sto8:     VG_(strcpy)(buffer, "1Sto8");  return;
        case Iop_1Sto16:    VG_(strcpy)(buffer, "1Sto16");  return;
        case Iop_1Sto32:    VG_(strcpy)(buffer, "1Sto32");  return;
        case Iop_1Sto64:    VG_(strcpy)(buffer, "1Sto64");  return;

        case Iop_MullS8:    VG_(strcpy)(buffer, "MullS8");  return;
        case Iop_MullS16:  VG_(strcpy)(buffer, "MullS16"); return;
        case Iop_MullS32:  VG_(strcpy)(buffer, "MullS32"); return;
        case Iop_MullS64:  VG_(strcpy)(buffer, "MullS64"); return;
        case Iop_MullU8:    VG_(strcpy)(buffer, "MullU8");  return;
        case Iop_MullU16:  VG_(strcpy)(buffer, "MullU16"); return;
        case Iop_MullU32:  VG_(strcpy)(buffer, "MullU32"); return;
        case Iop_MullU64:  VG_(strcpy)(buffer, "MullU64"); return;

        case Iop_Clz64:     VG_(strcpy)(buffer, "Clz64"); return;
        case Iop_Clz32:     VG_(strcpy)(buffer, "Clz32"); return;
        case Iop_Ctz64:     VG_(strcpy)(buffer, "Ctz64"); return;
        case Iop_Ctz32:     VG_(strcpy)(buffer, "Ctz32"); return;

        case Iop_CmpLT32S: VG_(strcpy)(buffer, "CmpLT32S"); return;
        case Iop_CmpLE32S: VG_(strcpy)(buffer, "CmpLE32S"); return;
        case Iop_CmpLT32U: VG_(strcpy)(buffer, "CmpLT32U"); return;
        case Iop_CmpLE32U: VG_(strcpy)(buffer, "CmpLE32U"); return;

        case Iop_CmpLT64S: VG_(strcpy)(buffer, "CmpLT64S"); return;
        case Iop_CmpLE64S: VG_(strcpy)(buffer, "CmpLE64S"); return;
        case Iop_CmpLT64U: VG_(strcpy)(buffer, "CmpLT64U"); return;
        case Iop_CmpLE64U: VG_(strcpy)(buffer, "CmpLE64U"); return;

        case Iop_CmpNEZ8:  VG_(strcpy)(buffer, "CmpNEZ8"); return;
        case Iop_CmpNEZ16: VG_(strcpy)(buffer, "CmpNEZ16"); return;
        case Iop_CmpNEZ32: VG_(strcpy)(buffer, "CmpNEZ32"); return;
        case Iop_CmpNEZ64: VG_(strcpy)(buffer, "CmpNEZ64"); return;

        case Iop_CmpwNEZ32: VG_(strcpy)(buffer, "CmpwNEZ32"); return;
        case Iop_CmpwNEZ64: VG_(strcpy)(buffer, "CmpwNEZ64"); return;

        case Iop_Left8:  VG_(strcpy)(buffer, "Left8"); return;
        case Iop_Left16: VG_(strcpy)(buffer, "Left16"); return;
        case Iop_Left32: VG_(strcpy)(buffer, "Left32"); return;
        case Iop_Left64: VG_(strcpy)(buffer, "Left64"); return;

        case Iop_CmpORD32U: VG_(strcpy)(buffer, "CmpORD32U"); return;
        case Iop_CmpORD32S: VG_(strcpy)(buffer, "CmpORD32S"); return;

        case Iop_CmpORD64U: VG_(strcpy)(buffer, "CmpORD64U"); return;
        case Iop_CmpORD64S: VG_(strcpy)(buffer, "CmpORD64S"); return;

        case Iop_DivU32: VG_(strcpy)(buffer, "DivU32"); return;
        case Iop_DivS32: VG_(strcpy)(buffer, "DivS32"); return;
        case Iop_DivU64: VG_(strcpy)(buffer, "DivU64"); return;
        case Iop_DivS64: VG_(strcpy)(buffer, "DivS64"); return;

        case Iop_DivModU64to32: VG_(strcpy)(buffer, "DivModU64to32"); return;
        case Iop_DivModS64to32: VG_(strcpy)(buffer, "DivModS64to32"); return;

        case Iop_DivModU128to64: VG_(strcpy)(buffer, "DivModU128to64"); return;
        case Iop_DivModS128to64: VG_(strcpy)(buffer, "DivModS128to64"); return;

        case Iop_16HIto8:  VG_(strcpy)(buffer, "16HIto8"); return;
        case Iop_16to8:     VG_(strcpy)(buffer, "16to8");    return;
        case Iop_8HLto16:  VG_(strcpy)(buffer, "8HLto16"); return;

        case Iop_32HIto16: VG_(strcpy)(buffer, "32HIto16"); return;
        case Iop_32to16:    VG_(strcpy)(buffer, "32to16");    return;
        case Iop_16HLto32: VG_(strcpy)(buffer, "16HLto32"); return;

        case Iop_64HIto32: VG_(strcpy)(buffer, "64HIto32"); return;
        case Iop_64to32:    VG_(strcpy)(buffer, "64to32");    return;
        case Iop_32HLto64: VG_(strcpy)(buffer, "32HLto64"); return;

        case Iop_128HIto64: VG_(strcpy)(buffer, "128HIto64"); return;
        case Iop_128to64:    VG_(strcpy)(buffer, "128to64");    return;
        case Iop_64HLto128: VG_(strcpy)(buffer, "64HLto128"); return;

        case Iop_AddF64:     VG_(strcpy)(buffer, "AddF64"); return;
        case Iop_SubF64:     VG_(strcpy)(buffer, "SubF64"); return;
        case Iop_MulF64:     VG_(strcpy)(buffer, "MulF64"); return;
        case Iop_DivF64:     VG_(strcpy)(buffer, "DivF64"); return;
        case Iop_AddF64r32: VG_(strcpy)(buffer, "AddF64r32"); return;
        case Iop_SubF64r32: VG_(strcpy)(buffer, "SubF64r32"); return;
        case Iop_MulF64r32: VG_(strcpy)(buffer, "MulF64r32"); return;
        case Iop_DivF64r32: VG_(strcpy)(buffer, "DivF64r32"); return;

        case Iop_ScaleF64:        VG_(strcpy)(buffer, "ScaleF64"); return;
        case Iop_AtanF64:         VG_(strcpy)(buffer, "AtanF64"); return;
        case Iop_Yl2xF64:         VG_(strcpy)(buffer, "Yl2xF64"); return;
        case Iop_Yl2xp1F64:      VG_(strcpy)(buffer, "Yl2xp1F64"); return;
        case Iop_PRemF64:         VG_(strcpy)(buffer, "PRemF64"); return;
        case Iop_PRemC3210F64:  VG_(strcpy)(buffer, "PRemC3210F64"); return;
        case Iop_PRem1F64:        VG_(strcpy)(buffer, "PRem1F64"); return;
        case Iop_PRem1C3210F64: VG_(strcpy)(buffer, "PRem1C3210F64"); return;
        case Iop_NegF64:          VG_(strcpy)(buffer, "NegF64"); return;
        case Iop_SqrtF64:         VG_(strcpy)(buffer, "SqrtF64"); return;

        case Iop_AbsF64:     VG_(strcpy)(buffer, "AbsF64"); return;
        case Iop_SinF64:     VG_(strcpy)(buffer, "SinF64"); return;
        case Iop_CosF64:     VG_(strcpy)(buffer, "CosF64"); return;
        case Iop_TanF64:     VG_(strcpy)(buffer, "TanF64"); return;
        case Iop_2xm1F64:    VG_(strcpy)(buffer, "2xm1F64"); return;

        case Iop_MAddF64:     VG_(strcpy)(buffer, "MAddF64"); return;
        case Iop_MSubF64:     VG_(strcpy)(buffer, "MSubF64"); return;
        case Iop_MAddF64r32: VG_(strcpy)(buffer, "MAddF64r32"); return;
        case Iop_MSubF64r32: VG_(strcpy)(buffer, "MSubF64r32"); return;

        case Iop_Est5FRSqrt:     VG_(strcpy)(buffer, "Est5FRSqrt"); return;
        case Iop_TruncF64asF32: VG_(strcpy)(buffer, "TruncF64asF32"); return;
        case Iop_CalcFPRF:        VG_(strcpy)(buffer, "CalcFPRF"); return;

        case Iop_CmpF64:     VG_(strcpy)(buffer, "CmpF64"); return;

        case Iop_F64toI16: VG_(strcpy)(buffer, "F64toI16"); return;
        case Iop_F64toI32: VG_(strcpy)(buffer, "F64toI32"); return;
        case Iop_F64toI64: VG_(strcpy)(buffer, "F64toI64"); return;

        case Iop_I16toF64: VG_(strcpy)(buffer, "I16toF64"); return;
        case Iop_I32toF64: VG_(strcpy)(buffer, "I32toF64"); return;
        case Iop_I64toF64: VG_(strcpy)(buffer, "I64toF64"); return;

        case Iop_F32toF64: VG_(strcpy)(buffer, "F32toF64"); return;
        case Iop_F64toF32: VG_(strcpy)(buffer, "F64toF32"); return;

        case Iop_RoundF64toInt: VG_(strcpy)(buffer, "RoundF64toInt"); return;
        case Iop_RoundF64toF32: VG_(strcpy)(buffer, "RoundF64toF32"); return;

        case Iop_ReinterpF64asI64: VG_(strcpy)(buffer, "ReinterpF64asI64"); return;
        case Iop_ReinterpI64asF64: VG_(strcpy)(buffer, "ReinterpI64asF64"); return;
        case Iop_ReinterpF32asI32: VG_(strcpy)(buffer, "ReinterpF32asI32"); return;
        case Iop_ReinterpI32asF32: VG_(strcpy)(buffer, "ReinterpI32asF32"); return;

        case Iop_I32UtoFx4: VG_(strcpy)(buffer, "Iop_I32UtoFx4"); return;
        case Iop_I32StoFx4: VG_(strcpy)(buffer, "Iop_I32StoFx4"); return;

        case Iop_QFtoI32Ux4_RZ: VG_(strcpy)(buffer, "Iop_QFtoI32Ux4_RZ"); return;
        case Iop_QFtoI32Sx4_RZ: VG_(strcpy)(buffer, "Iop_QFtoI32Sx4_RZ"); return;

        case Iop_RoundF32x4_RM: VG_(strcpy)(buffer, "Iop_RoundF32x4_RM"); return;
        case Iop_RoundF32x4_RP: VG_(strcpy)(buffer, "Iop_RoundF32x4_RP"); return;
        case Iop_RoundF32x4_RN: VG_(strcpy)(buffer, "Iop_RoundF32x4_RN"); return;
        case Iop_RoundF32x4_RZ: VG_(strcpy)(buffer, "Iop_RoundF32x4_RZ"); return;

        case Iop_Add8x8: VG_(strcpy)(buffer, "Add8x8"); return;
        case Iop_Add16x4: VG_(strcpy)(buffer, "Add16x4"); return;
        case Iop_Add32x2: VG_(strcpy)(buffer, "Add32x2"); return;
        case Iop_QAdd8Ux8: VG_(strcpy)(buffer, "QAdd8Ux8"); return;
        case Iop_QAdd16Ux4: VG_(strcpy)(buffer, "QAdd16Ux4"); return;
        case Iop_QAdd8Sx8: VG_(strcpy)(buffer, "QAdd8Sx8"); return;
        case Iop_QAdd16Sx4: VG_(strcpy)(buffer, "QAdd16Sx4"); return;
        case Iop_Sub8x8: VG_(strcpy)(buffer, "Sub8x8"); return;
        case Iop_Sub16x4: VG_(strcpy)(buffer, "Sub16x4"); return;
        case Iop_Sub32x2: VG_(strcpy)(buffer, "Sub32x2"); return;
        case Iop_QSub8Ux8: VG_(strcpy)(buffer, "QSub8Ux8"); return;
        case Iop_QSub16Ux4: VG_(strcpy)(buffer, "QSub16Ux4"); return;
        case Iop_QSub8Sx8: VG_(strcpy)(buffer, "QSub8Sx8"); return;
        case Iop_QSub16Sx4: VG_(strcpy)(buffer, "QSub16Sx4"); return;
        case Iop_Mul16x4: VG_(strcpy)(buffer, "Mul16x4"); return;
        case Iop_Mul32x2: VG_(strcpy)(buffer, "Mul32x2"); return;
        case Iop_MulHi16Ux4: VG_(strcpy)(buffer, "MulHi16Ux4"); return;
        case Iop_MulHi16Sx4: VG_(strcpy)(buffer, "MulHi16Sx4"); return;
        case Iop_Avg8Ux8: VG_(strcpy)(buffer, "Avg8Ux8"); return;
        case Iop_Avg16Ux4: VG_(strcpy)(buffer, "Avg16Ux4"); return;
        case Iop_Max16Sx4: VG_(strcpy)(buffer, "Max16Sx4"); return;
        case Iop_Max8Ux8: VG_(strcpy)(buffer, "Max8Ux8"); return;
        case Iop_Min16Sx4: VG_(strcpy)(buffer, "Min16Sx4"); return;
        case Iop_Min8Ux8: VG_(strcpy)(buffer, "Min8Ux8"); return;
        case Iop_CmpEQ8x8: VG_(strcpy)(buffer, "CmpEQ8x8"); return;
        case Iop_CmpEQ16x4: VG_(strcpy)(buffer, "CmpEQ16x4"); return;
        case Iop_CmpEQ32x2: VG_(strcpy)(buffer, "CmpEQ32x2"); return;
        case Iop_CmpGT8Sx8: VG_(strcpy)(buffer, "CmpGT8Sx8"); return;
        case Iop_CmpGT16Sx4: VG_(strcpy)(buffer, "CmpGT16Sx4"); return;
        case Iop_CmpGT32Sx2: VG_(strcpy)(buffer, "CmpGT32Sx2"); return;
        case Iop_ShlN8x8: VG_(strcpy)(buffer, "ShlN8x8"); return;
        case Iop_ShlN16x4: VG_(strcpy)(buffer, "ShlN16x4"); return;
        case Iop_ShlN32x2: VG_(strcpy)(buffer, "ShlN32x2"); return;
        case Iop_ShrN16x4: VG_(strcpy)(buffer, "ShrN16x4"); return;
        case Iop_ShrN32x2: VG_(strcpy)(buffer, "ShrN32x2"); return;
        case Iop_SarN8x8: VG_(strcpy)(buffer, "SarN8x8"); return;
        case Iop_SarN16x4: VG_(strcpy)(buffer, "SarN16x4"); return;
        case Iop_SarN32x2: VG_(strcpy)(buffer, "SarN32x2"); return;
        case Iop_QNarrow16Ux4: VG_(strcpy)(buffer, "QNarrow16Ux4"); return;
        case Iop_QNarrow16Sx4: VG_(strcpy)(buffer, "QNarrow16Sx4"); return;
        case Iop_QNarrow32Sx2: VG_(strcpy)(buffer, "QNarrow32Sx2"); return;
        case Iop_InterleaveHI8x8: VG_(strcpy)(buffer, "InterleaveHI8x8"); return;
        case Iop_InterleaveHI16x4: VG_(strcpy)(buffer, "InterleaveHI16x4"); return;
        case Iop_InterleaveHI32x2: VG_(strcpy)(buffer, "InterleaveHI32x2"); return;
        case Iop_InterleaveLO8x8: VG_(strcpy)(buffer, "InterleaveLO8x8"); return;
        case Iop_InterleaveLO16x4: VG_(strcpy)(buffer, "InterleaveLO16x4"); return;
        case Iop_InterleaveLO32x2: VG_(strcpy)(buffer, "InterleaveLO32x2"); return;
        case Iop_CatOddLanes16x4: VG_(strcpy)(buffer, "CatOddLanes16x4"); return;
        case Iop_CatEvenLanes16x4: VG_(strcpy)(buffer, "CatEvenLanes16x4"); return;
        case Iop_Perm8x8: VG_(strcpy)(buffer, "Iop_Perm8x8"); return;

        case Iop_CmpNEZ32x2: VG_(strcpy)(buffer, "CmpNEZ32x2"); return;
        case Iop_CmpNEZ16x4: VG_(strcpy)(buffer, "CmpNEZ16x4"); return;
        case Iop_CmpNEZ8x8:  VG_(strcpy)(buffer, "CmpNEZ8x8"); return;

        case Iop_Add32Fx4:  VG_(strcpy)(buffer, "Add32Fx4"); return;
        case Iop_Add32F0x4: VG_(strcpy)(buffer, "Add32F0x4"); return;
        case Iop_Add64Fx2:  VG_(strcpy)(buffer, "Add64Fx2"); return;
        case Iop_Add64F0x2: VG_(strcpy)(buffer, "Add64F0x2"); return;

        case Iop_Div32Fx4:  VG_(strcpy)(buffer, "Div32Fx4"); return;
        case Iop_Div32F0x4: VG_(strcpy)(buffer, "Div32F0x4"); return;
        case Iop_Div64Fx2:  VG_(strcpy)(buffer, "Div64Fx2"); return;
        case Iop_Div64F0x2: VG_(strcpy)(buffer, "Div64F0x2"); return;

        case Iop_Max32Fx4:  VG_(strcpy)(buffer, "Max32Fx4"); return;
        case Iop_Max32F0x4: VG_(strcpy)(buffer, "Max32F0x4"); return;
        case Iop_Max64Fx2:  VG_(strcpy)(buffer, "Max64Fx2"); return;
        case Iop_Max64F0x2: VG_(strcpy)(buffer, "Max64F0x2"); return;

        case Iop_Min32Fx4:  VG_(strcpy)(buffer, "Min32Fx4"); return;
        case Iop_Min32F0x4: VG_(strcpy)(buffer, "Min32F0x4"); return;
        case Iop_Min64Fx2:  VG_(strcpy)(buffer, "Min64Fx2"); return;
        case Iop_Min64F0x2: VG_(strcpy)(buffer, "Min64F0x2"); return;

        case Iop_Mul32Fx4:  VG_(strcpy)(buffer, "Mul32Fx4"); return;
        case Iop_Mul32F0x4: VG_(strcpy)(buffer, "Mul32F0x4"); return;
        case Iop_Mul64Fx2:  VG_(strcpy)(buffer, "Mul64Fx2"); return;
        case Iop_Mul64F0x2: VG_(strcpy)(buffer, "Mul64F0x2"); return;

        case Iop_Recip32Fx4:  VG_(strcpy)(buffer, "Recip32Fx4"); return;
        case Iop_Recip32F0x4: VG_(strcpy)(buffer, "Recip32F0x4"); return;
        case Iop_Recip64Fx2:  VG_(strcpy)(buffer, "Recip64Fx2"); return;
        case Iop_Recip64F0x2: VG_(strcpy)(buffer, "Recip64F0x2"); return;

        case Iop_RSqrt32Fx4:  VG_(strcpy)(buffer, "RSqrt32Fx4"); return;
        case Iop_RSqrt32F0x4: VG_(strcpy)(buffer, "RSqrt32F0x4"); return;
        case Iop_RSqrt64Fx2:  VG_(strcpy)(buffer, "RSqrt64Fx2"); return;
        case Iop_RSqrt64F0x2: VG_(strcpy)(buffer, "RSqrt64F0x2"); return;

        case Iop_Sqrt32Fx4:  VG_(strcpy)(buffer, "Sqrt32Fx4"); return;
        case Iop_Sqrt32F0x4: VG_(strcpy)(buffer, "Sqrt32F0x4"); return;
        case Iop_Sqrt64Fx2:  VG_(strcpy)(buffer, "Sqrt64Fx2"); return;
        case Iop_Sqrt64F0x2: VG_(strcpy)(buffer, "Sqrt64F0x2"); return;

        case Iop_Sub32Fx4:  VG_(strcpy)(buffer, "Sub32Fx4"); return;
        case Iop_Sub32F0x4: VG_(strcpy)(buffer, "Sub32F0x4"); return;
        case Iop_Sub64Fx2:  VG_(strcpy)(buffer, "Sub64Fx2"); return;
        case Iop_Sub64F0x2: VG_(strcpy)(buffer, "Sub64F0x2"); return;

        case Iop_CmpEQ32Fx4: VG_(strcpy)(buffer, "CmpEQ32Fx4"); return;
        case Iop_CmpLT32Fx4: VG_(strcpy)(buffer, "CmpLT32Fx4"); return;
        case Iop_CmpLE32Fx4: VG_(strcpy)(buffer, "CmpLE32Fx4"); return;
        case Iop_CmpGT32Fx4: VG_(strcpy)(buffer, "CmpGT32Fx4"); return;
        case Iop_CmpGE32Fx4: VG_(strcpy)(buffer, "CmpGE32Fx4"); return;
        case Iop_CmpUN32Fx4: VG_(strcpy)(buffer, "CmpUN32Fx4"); return;
        case Iop_CmpEQ64Fx2: VG_(strcpy)(buffer, "CmpEQ64Fx2"); return;
        case Iop_CmpLT64Fx2: VG_(strcpy)(buffer, "CmpLT64Fx2"); return;
        case Iop_CmpLE64Fx2: VG_(strcpy)(buffer, "CmpLE64Fx2"); return;
        case Iop_CmpUN64Fx2: VG_(strcpy)(buffer, "CmpUN64Fx2"); return;

        case Iop_CmpEQ32F0x4: VG_(strcpy)(buffer, "CmpEQ32F0x4"); return;
        case Iop_CmpLT32F0x4: VG_(strcpy)(buffer, "CmpLT32F0x4"); return;
        case Iop_CmpLE32F0x4: VG_(strcpy)(buffer, "CmpLE32F0x4"); return;
        case Iop_CmpUN32F0x4: VG_(strcpy)(buffer, "CmpUN32F0x4"); return;
        case Iop_CmpEQ64F0x2: VG_(strcpy)(buffer, "CmpEQ64F0x2"); return;
        case Iop_CmpLT64F0x2: VG_(strcpy)(buffer, "CmpLT64F0x2"); return;
        case Iop_CmpLE64F0x2: VG_(strcpy)(buffer, "CmpLE64F0x2"); return;
        case Iop_CmpUN64F0x2: VG_(strcpy)(buffer, "CmpUN64F0x2"); return;

        case Iop_V128to64:    VG_(strcpy)(buffer, "V128to64");    return;
        case Iop_V128HIto64: VG_(strcpy)(buffer, "V128HIto64"); return;
        case Iop_64HLtoV128: VG_(strcpy)(buffer, "64HLtoV128"); return;

        case Iop_64UtoV128:    VG_(strcpy)(buffer, "64UtoV128"); return;
        case Iop_SetV128lo64: VG_(strcpy)(buffer, "SetV128lo64"); return;

        case Iop_32UtoV128:    VG_(strcpy)(buffer, "32UtoV128"); return;
        case Iop_V128to32:     VG_(strcpy)(buffer, "V128to32"); return;
        case Iop_SetV128lo32: VG_(strcpy)(buffer, "SetV128lo32"); return;

        case Iop_Dup8x16: VG_(strcpy)(buffer, "Dup8x16"); return;
        case Iop_Dup16x8: VG_(strcpy)(buffer, "Dup16x8"); return;
        case Iop_Dup32x4: VG_(strcpy)(buffer, "Dup32x4"); return;

        case Iop_NotV128:     VG_(strcpy)(buffer, "NotV128"); return;
        case Iop_AndV128:     VG_(strcpy)(buffer, "AndV128"); return;
        case Iop_OrV128:      VG_(strcpy)(buffer, "OrV128");  return;
        case Iop_XorV128:     VG_(strcpy)(buffer, "XorV128"); return;

        case Iop_CmpNEZ8x16: VG_(strcpy)(buffer, "CmpNEZ8x16"); return;
        case Iop_CmpNEZ16x8: VG_(strcpy)(buffer, "CmpNEZ16x8"); return;
        case Iop_CmpNEZ32x4: VG_(strcpy)(buffer, "CmpNEZ32x4"); return;
        case Iop_CmpNEZ64x2: VG_(strcpy)(buffer, "CmpNEZ64x2"); return;

        case Iop_Add8x16:    VG_(strcpy)(buffer, "Add8x16"); return;
        case Iop_Add16x8:    VG_(strcpy)(buffer, "Add16x8"); return;
        case Iop_Add32x4:    VG_(strcpy)(buffer, "Add32x4"); return;
        case Iop_Add64x2:    VG_(strcpy)(buffer, "Add64x2"); return;
        case Iop_QAdd8Ux16: VG_(strcpy)(buffer, "QAdd8Ux16"); return;
        case Iop_QAdd16Ux8: VG_(strcpy)(buffer, "QAdd16Ux8"); return;
        case Iop_QAdd32Ux4: VG_(strcpy)(buffer, "QAdd32Ux4"); return;
        case Iop_QAdd8Sx16: VG_(strcpy)(buffer, "QAdd8Sx16"); return;
        case Iop_QAdd16Sx8: VG_(strcpy)(buffer, "QAdd16Sx8"); return;
        case Iop_QAdd32Sx4: VG_(strcpy)(buffer, "QAdd32Sx4"); return;

        case Iop_Sub8x16:    VG_(strcpy)(buffer, "Sub8x16"); return;
        case Iop_Sub16x8:    VG_(strcpy)(buffer, "Sub16x8"); return;
        case Iop_Sub32x4:    VG_(strcpy)(buffer, "Sub32x4"); return;
        case Iop_Sub64x2:    VG_(strcpy)(buffer, "Sub64x2"); return;
        case Iop_QSub8Ux16: VG_(strcpy)(buffer, "QSub8Ux16"); return;
        case Iop_QSub16Ux8: VG_(strcpy)(buffer, "QSub16Ux8"); return;
        case Iop_QSub32Ux4: VG_(strcpy)(buffer, "QSub32Ux4"); return;
        case Iop_QSub8Sx16: VG_(strcpy)(buffer, "QSub8Sx16"); return;
        case Iop_QSub16Sx8: VG_(strcpy)(buffer, "QSub16Sx8"); return;
        case Iop_QSub32Sx4: VG_(strcpy)(buffer, "QSub32Sx4"); return;

        case Iop_Mul16x8:     VG_(strcpy)(buffer, "Mul16x8"); return;
        case Iop_MulHi16Ux8: VG_(strcpy)(buffer, "MulHi16Ux8"); return;
        case Iop_MulHi32Ux4: VG_(strcpy)(buffer, "MulHi32Ux4"); return;
        case Iop_MulHi16Sx8: VG_(strcpy)(buffer, "MulHi16Sx8"); return;
        case Iop_MulHi32Sx4: VG_(strcpy)(buffer, "MulHi32Sx4"); return;

        case Iop_MullEven8Ux16: VG_(strcpy)(buffer, "MullEven8Ux16"); return;
        case Iop_MullEven16Ux8: VG_(strcpy)(buffer, "MullEven16Ux8"); return;
        case Iop_MullEven8Sx16: VG_(strcpy)(buffer, "MullEven8Sx16"); return;
        case Iop_MullEven16Sx8: VG_(strcpy)(buffer, "MullEven16Sx8"); return;

        case Iop_Avg8Ux16: VG_(strcpy)(buffer, "Avg8Ux16"); return;
        case Iop_Avg16Ux8: VG_(strcpy)(buffer, "Avg16Ux8"); return;
        case Iop_Avg32Ux4: VG_(strcpy)(buffer, "Avg32Ux4"); return;
        case Iop_Avg8Sx16: VG_(strcpy)(buffer, "Avg8Sx16"); return;
        case Iop_Avg16Sx8: VG_(strcpy)(buffer, "Avg16Sx8"); return;
        case Iop_Avg32Sx4: VG_(strcpy)(buffer, "Avg32Sx4"); return;

        case Iop_Max8Sx16: VG_(strcpy)(buffer, "Max8Sx16"); return;
        case Iop_Max16Sx8: VG_(strcpy)(buffer, "Max16Sx8"); return;
        case Iop_Max32Sx4: VG_(strcpy)(buffer, "Max32Sx4"); return;
        case Iop_Max8Ux16: VG_(strcpy)(buffer, "Max8Ux16"); return;
        case Iop_Max16Ux8: VG_(strcpy)(buffer, "Max16Ux8"); return;
        case Iop_Max32Ux4: VG_(strcpy)(buffer, "Max32Ux4"); return;

        case Iop_Min8Sx16: VG_(strcpy)(buffer, "Min8Sx16"); return;
        case Iop_Min16Sx8: VG_(strcpy)(buffer, "Min16Sx8"); return;
        case Iop_Min32Sx4: VG_(strcpy)(buffer, "Min32Sx4"); return;
        case Iop_Min8Ux16: VG_(strcpy)(buffer, "Min8Ux16"); return;
        case Iop_Min16Ux8: VG_(strcpy)(buffer, "Min16Ux8"); return;
        case Iop_Min32Ux4: VG_(strcpy)(buffer, "Min32Ux4"); return;

        case Iop_CmpEQ8x16:  VG_(strcpy)(buffer, "CmpEQ8x16"); return;
        case Iop_CmpEQ16x8:  VG_(strcpy)(buffer, "CmpEQ16x8"); return;
        case Iop_CmpEQ32x4:  VG_(strcpy)(buffer, "CmpEQ32x4"); return;
        case Iop_CmpGT8Sx16: VG_(strcpy)(buffer, "CmpGT8Sx16"); return;
        case Iop_CmpGT16Sx8: VG_(strcpy)(buffer, "CmpGT16Sx8"); return;
        case Iop_CmpGT32Sx4: VG_(strcpy)(buffer, "CmpGT32Sx4"); return;
        case Iop_CmpGT8Ux16: VG_(strcpy)(buffer, "CmpGT8Ux16"); return;
        case Iop_CmpGT16Ux8: VG_(strcpy)(buffer, "CmpGT16Ux8"); return;
        case Iop_CmpGT32Ux4: VG_(strcpy)(buffer, "CmpGT32Ux4"); return;

        case Iop_ShlV128: VG_(strcpy)(buffer, "ShlV128"); return;
        case Iop_ShrV128: VG_(strcpy)(buffer, "ShrV128"); return;

        case Iop_ShlN8x16: VG_(strcpy)(buffer, "ShlN8x16"); return;
        case Iop_ShlN16x8: VG_(strcpy)(buffer, "ShlN16x8"); return;
        case Iop_ShlN32x4: VG_(strcpy)(buffer, "ShlN32x4"); return;
        case Iop_ShlN64x2: VG_(strcpy)(buffer, "ShlN64x2"); return;
        case Iop_ShrN8x16: VG_(strcpy)(buffer, "ShrN8x16"); return;
        case Iop_ShrN16x8: VG_(strcpy)(buffer, "ShrN16x8"); return;
        case Iop_ShrN32x4: VG_(strcpy)(buffer, "ShrN32x4"); return;
        case Iop_ShrN64x2: VG_(strcpy)(buffer, "ShrN64x2"); return;
        case Iop_SarN8x16: VG_(strcpy)(buffer, "SarN8x16"); return;
        case Iop_SarN16x8: VG_(strcpy)(buffer, "SarN16x8"); return;
        case Iop_SarN32x4: VG_(strcpy)(buffer, "SarN32x4"); return;

        case Iop_Shl8x16: VG_(strcpy)(buffer, "Shl8x16"); return;
        case Iop_Shl16x8: VG_(strcpy)(buffer, "Shl16x8"); return;
        case Iop_Shl32x4: VG_(strcpy)(buffer, "Shl32x4"); return;
        case Iop_Shr8x16: VG_(strcpy)(buffer, "Shr8x16"); return;
        case Iop_Shr16x8: VG_(strcpy)(buffer, "Shr16x8"); return;
        case Iop_Shr32x4: VG_(strcpy)(buffer, "Shr32x4"); return;
        case Iop_Sar8x16: VG_(strcpy)(buffer, "Sar8x16"); return;
        case Iop_Sar16x8: VG_(strcpy)(buffer, "Sar16x8"); return;
        case Iop_Sar32x4: VG_(strcpy)(buffer, "Sar32x4"); return;
        case Iop_Rol8x16: VG_(strcpy)(buffer, "Rol8x16"); return;
        case Iop_Rol16x8: VG_(strcpy)(buffer, "Rol16x8"); return;
        case Iop_Rol32x4: VG_(strcpy)(buffer, "Rol32x4"); return;

        case Iop_Narrow16x8:    VG_(strcpy)(buffer, "Narrow16x8"); return;
        case Iop_Narrow32x4:    VG_(strcpy)(buffer, "Narrow32x4"); return;
        case Iop_QNarrow16Ux8: VG_(strcpy)(buffer, "QNarrow16Ux8"); return;
        case Iop_QNarrow32Ux4: VG_(strcpy)(buffer, "QNarrow32Ux4"); return;
        case Iop_QNarrow16Sx8: VG_(strcpy)(buffer, "QNarrow16Sx8"); return;
        case Iop_QNarrow32Sx4: VG_(strcpy)(buffer, "QNarrow32Sx4"); return;

        case Iop_InterleaveHI8x16: VG_(strcpy)(buffer, "InterleaveHI8x16"); return;
        case Iop_InterleaveHI16x8: VG_(strcpy)(buffer, "InterleaveHI16x8"); return;
        case Iop_InterleaveHI32x4: VG_(strcpy)(buffer, "InterleaveHI32x4"); return;
        case Iop_InterleaveHI64x2: VG_(strcpy)(buffer, "InterleaveHI64x2"); return;
        case Iop_InterleaveLO8x16: VG_(strcpy)(buffer, "InterleaveLO8x16"); return;
        case Iop_InterleaveLO16x8: VG_(strcpy)(buffer, "InterleaveLO16x8"); return;
        case Iop_InterleaveLO32x4: VG_(strcpy)(buffer, "InterleaveLO32x4"); return;
        case Iop_InterleaveLO64x2: VG_(strcpy)(buffer, "InterleaveLO64x2"); return;

        case Iop_Perm8x16: VG_(strcpy)(buffer, "Perm8x16"); return;

        default: VG_(tool_panic)("ppIROp(1)");
    }

    VG_(strcpy)(buffer, str);
    switch (op - base) {
        case 0:
            VG_(strcat)(buffer, "8");
            break;
        case 1:
            VG_(strcat)(buffer, "16");
            break;
        case 2:
            VG_(strcat)(buffer, "32");
            break;
        case 3:
            VG_(strcat)(buffer, "64");
            break;
        default:
            VG_(tool_panic)("IROp_to_str(2)");
    }
}
