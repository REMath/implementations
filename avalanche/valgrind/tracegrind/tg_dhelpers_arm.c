#if defined(VGP_arm_linux)

#include "pub_tool_basics.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_mallocfree.h"
#include "libvex_ir.h"

#include <avalanche.h>

enum 
{
  ARMCondEQ, ARMCondNE, ARMCondHS, ARMCondLO,
  ARMCondMI, ARMCondPL, ARMCondVS, ARMCondVC,
  ARMCondHI, ARMCondLS, ARMCondGE, ARMCondLT,
  ARMCondGT, ARMCondLE, ARMCondAL, ARMCondNV
};

extern void instrumentWrTmpCCall_Internal(UInt op, UInt ltmp, 
                                          UShort taintedness, 
                                          const Char* bitVectorModifier,
                                          IRExpr* arg1, IRExpr* arg2,
                                          IRExpr* value1, IRExpr* value2);

extern void instrumentWrTmpLongBinop_Internal(UInt oprt, UInt ltmp,
                                              UShort taintedness,
                                              IRExpr* arg1, IRExpr* arg2,
                                              ULong value1, ULong value2);

extern UShort isPropagation2(IRExpr* arg1, IRExpr* arg2);
extern Bool firstTainted(UShort res);
extern Bool secondTainted(UShort res);

IRExpr* adjustSize(IRSB* sbOut, IRTypeEnv* tyenv, IRExpr* arg)
{
  if (arg == NULL) {
    return NULL;
  }
  IRTemp tmp;
  IRExpr* e;
  IRType argty = typeOfIRExpr(tyenv, arg);
  switch (argty)
  {
    case Ity_I1: 
       tmp = newIRTemp(tyenv, Ity_I32);
       e = IRExpr_Unop(Iop_1Uto32, arg);
       addStmtToIRSB(sbOut, IRStmt_WrTmp(tmp, e));
       return IRExpr_RdTmp(tmp);
    case Ity_I8:
       tmp = newIRTemp(tyenv, Ity_I32);
       e = IRExpr_Unop(Iop_8Uto32, arg);
       addStmtToIRSB(sbOut, IRStmt_WrTmp(tmp, e));
       return IRExpr_RdTmp(tmp);
    case Ity_I16:
       tmp = newIRTemp(tyenv, Ity_I32);
       e = IRExpr_Unop(Iop_16Uto32, arg);
       addStmtToIRSB(sbOut, IRStmt_WrTmp(tmp, e));
       return IRExpr_RdTmp(tmp);
    case Ity_I32:
       return arg;
    case Ity_I64:
       if (arg->tag == Iex_Const)
       {
         tmp = newIRTemp(tyenv, Ity_I64);
         e = IRExpr_Const(arg->Iex.Const.con);
         addStmtToIRSB(sbOut, IRStmt_WrTmp(tmp, e));
         return IRExpr_RdTmp(tmp);
       }
       return arg;
    default:
       return arg;
  }
}

static
UInt translateNativeCondCode(UInt nativeCC)
{
  switch(nativeCC)
  {
    case ARMCondLO: return BVLT;
    case ARMCondHS: return BVGE;
    case ARMCondEQ: return IFT;
    case ARMCondNE: return IFNOT;
    case ARMCondLS: return BVLE;
    case ARMCondHI: return BVGT;
    case ARMCondLT: return SBVLT;
    case ARMCondGE: return SBVGE;
    case ARMCondLE: return SBVLE;
    case ARMCondGT: return SBVGT;
    default:        return INVALID;
  }
}

static
void instrumentWrTmpCCall(IRStmt* clone, 
                          HWord value0, IRExpr* value1, IRExpr* value2)
{
  IRExpr* arg1 = clone->Ist.WrTmp.data->Iex.CCall.args[1];
  IRExpr* arg2 = clone->Ist.WrTmp.data->Iex.CCall.args[2];
  UShort taintedness = isPropagation2(arg1, arg2);
  if (taintedness)
  {
    UInt op = translateNativeCondCode(((UInt) value0) >> 4);
    UInt ltmp = clone->Ist.WrTmp.tmp;
    instrumentWrTmpCCall_Internal(op, ltmp, taintedness, "", 
                                  arg1, arg2, value1, value2);
  }
}

void instrumentWrTmpCCall_External(IRSB* sbOut, IRStmt* clone, 
                                   IRExpr* value0, IRExpr* value1, 
                                   IRExpr* value2, IRExpr* value3)
{

  if (!VG_(strcmp)(clone->Ist.WrTmp.data->Iex.CCall.cee->name,
                  "armg_calculate_condition") &&
      (value0 != NULL) && (value1 != NULL) && (value2 != NULL))

  {
    IRDirty* di = 
         unsafeIRDirty_0_N(0, "instrumentWrTmpCCall", 
                           VG_(fnptr_to_fnentry)(&instrumentWrTmpCCall), 
                           mkIRExprVec_4(mkIRExpr_HWord((HWord) clone),
                                         value0, value1, value2));
    addStmtToIRSB(sbOut, IRStmt_Dirty(di));
  }
}

/* Each LongBinop statement is instrumented two times consequently with
   (diCounter = 1, value = arg2_value) and (diCounter = 2, value = arg1_value).

   instrumentWrTmpLongBinop only does actual work if either
     diCounter == 1 AND arg1 is tainted
   OR
     diCounter == 2 AND arg2 is tainted AND arg1 is NOT tainted
   to ensure that no duplicates appear in tainted trace log.
*/

static
void instrumentWrTmpLongBinop(IRStmt* clone, IRExpr* diCounter, ULong value)
{
  IRExpr* arg1 = clone->Ist.WrTmp.data->Iex.Binop.arg1;
  IRExpr* arg2 = clone->Ist.WrTmp.data->Iex.Binop.arg2;
  UShort taintedness = isPropagation2(arg1, arg2);
  if (!taintedness)
  {
    return;
  }
  ULong value1, value2;
  UInt ltmp = clone->Ist.WrTmp.tmp;
  UInt oprt = clone->Ist.WrTmp.data->Iex.Binop.op;
  if (firstTainted(taintedness))
  {
    value1 = 0;
    value2 = value;
  }
  if (secondTainted(taintedness))
  {
    value1 = value;
    value2 = 1;
  }
  if ((firstTainted(taintedness) && (diCounter == 1)) || 
      (secondTainted(taintedness) && (diCounter == 2) && 
       !firstTainted(taintedness)))
  {
    instrumentWrTmpLongBinop_Internal(oprt, ltmp, taintedness, 
                             arg1, arg2, value1, value2);
  }
}

void instrumentWrTmpLongBinop_External(IRSB* sbOut, IRStmt* clone, 
                                       IRExpr* value1, IRExpr* value2)
{
  IRDirty* di1 = 
       unsafeIRDirty_0_N(0, "instrumentWrTmpLongBinop",
                         VG_(fnptr_to_fnentry)(&instrumentWrTmpLongBinop),
                         mkIRExprVec_3(mkIRExpr_HWord((HWord) clone), 
                                       mkIRExpr_HWord(1), value2));
  IRDirty* di2 = 
       unsafeIRDirty_0_N(0, "instrumentWrTmpLongBinop",
                         VG_(fnptr_to_fnentry)(&instrumentWrTmpLongBinop),
                         mkIRExprVec_3(mkIRExpr_HWord((HWord) clone), 
                                       mkIRExpr_HWord(2), value1));
  addStmtToIRSB(sbOut, IRStmt_Dirty(di1));
  addStmtToIRSB(sbOut, IRStmt_Dirty(di2));
}

#endif
