
// Sixgill: Static assertion checker for C/C++ programs.
// Copyright (C) 2009-2010  Stanford University
// Author: Brian Hackett
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "exp.h"
#include "bit.h"
#include "storage.h"

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// Exp hash static
/////////////////////////////////////////////////////////////////////

void (*g_callback_ExpSimplify)(Exp*, Exp*) = NULL;
void (*g_callback_CvtSimplify)(Exp*, Bit*) = NULL;
void (*g_callback_BitSimplify)(Bit*, Bit*) = NULL;

HashCons<Exp> Exp::g_table;

int Exp::Compare(const Exp *exp0, const Exp *exp1)
{
  TryCompareValues(exp0->Kind(), exp1->Kind());
  TryCompareValues(exp0->Bits(), exp1->Bits());
  TryCompareValues(exp0->Sign(), exp1->Sign());

  switch (exp0->Kind()) {
  case EK_Empty:
    break;

  case EK_Var: {
    const ExpVar *nexp0 = exp0->AsVar();
    const ExpVar *nexp1 = exp1->AsVar();
    TryCompareObjects(nexp0->GetVariable(), nexp1->GetVariable(), Variable);
    break;
  }
  case EK_Drf: {
    const ExpDrf *nexp0 = exp0->AsDrf();
    const ExpDrf *nexp1 = exp1->AsDrf();
    TryCompareObjects(nexp0->GetTarget(), nexp1->GetTarget(), Exp);
    break;
  }
  case EK_Fld: {
    const ExpFld *nexp0 = exp0->AsFld();
    const ExpFld *nexp1 = exp1->AsFld();
    TryCompareObjects(nexp0->GetTarget(), nexp1->GetTarget(), Exp);
    TryCompareObjects(nexp0->GetField(), nexp1->GetField(), Field);
    break;
  }
  case EK_Rfld: {
    const ExpRfld *nexp0 = exp0->AsRfld();
    const ExpRfld *nexp1 = exp1->AsRfld();
    TryCompareObjects(nexp0->GetTarget(), nexp1->GetTarget(), Exp);
    TryCompareObjects(nexp0->GetField(), nexp1->GetField(), Field);
    break;
  }
  case EK_Index: {
    const ExpIndex *nexp0 = exp0->AsIndex();
    const ExpIndex *nexp1 = exp1->AsIndex();
    TryCompareObjects(nexp0->GetTarget(), nexp1->GetTarget(), Exp);
    TryCompareObjects(nexp0->GetElementType(), nexp1->GetElementType(), Type);
    TryCompareObjects(nexp0->GetIndex(), nexp1->GetIndex(), Exp);
    break;
  }
  case EK_String: {
    const ExpString *nexp0 = exp0->AsString();
    const ExpString *nexp1 = exp1->AsString();
    TryCompareObjects(nexp0->GetString(), nexp1->GetString(), DataString);
    break;
  }
  case EK_Clobber: {
    const ExpClobber *nexp0 = exp0->AsClobber();
    const ExpClobber *nexp1 = exp1->AsClobber();
    TryCompareObjects(nexp0->GetCallee(), nexp1->GetCallee(), Exp);
    TryCompareObjects(nexp0->GetValueKind(), nexp1->GetValueKind(), Exp);
    TryCompareObjects(nexp0->GetOverwrite(), nexp1->GetOverwrite(), Exp);
    TryCompareValues(nexp0->GetPoint(), nexp1->GetPoint());
    TryCompareObjects(nexp0->GetLocation(), nexp1->GetLocation(), Location);
    break;
  }

  case EK_Int: {
    const ExpInt *nexp0 = exp0->AsInt();
    const ExpInt *nexp1 = exp1->AsInt();
    return strcmp(nexp0->GetValue(), nexp1->GetValue());
  }
  case EK_Float: {
    const ExpFloat *nexp0 = exp0->AsFloat();
    const ExpFloat *nexp1 = exp1->AsFloat();
    return strcmp(nexp0->GetValue(), nexp1->GetValue());
  }
  case EK_Unop: {
    const ExpUnop *nexp0 = exp0->AsUnop();
    const ExpUnop *nexp1 = exp1->AsUnop();
    TryCompareValues(nexp0->GetUnopKind(), nexp1->GetUnopKind());
    TryCompareObjects(nexp0->GetOperand(), nexp1->GetOperand(), Exp);
    break;
  }
  case EK_Binop: {
    const ExpBinop *nexp0 = exp0->AsBinop();
    const ExpBinop *nexp1 = exp1->AsBinop();
    TryCompareValues(nexp0->GetBinopKind(), nexp1->GetBinopKind());
    TryCompareObjects(nexp0->GetLeftOperand(), nexp1->GetLeftOperand(), Exp);
    TryCompareObjects(nexp0->GetRightOperand(), nexp1->GetRightOperand(), Exp);
    TryCompareObjects(nexp0->GetStrideType(), nexp1->GetStrideType(), Type);
    break;
  }

  case EK_Exit: {
    const ExpExit *nexp0 = exp0->AsExit();
    const ExpExit *nexp1 = exp1->AsExit();
    TryCompareObjects(nexp0->GetTarget(), nexp1->GetTarget(), Exp);
    TryCompareObjects(nexp0->GetValueKind(), nexp1->GetValueKind(), Exp);
    break;
  }
  case EK_Initial: {
    const ExpInitial *nexp0 = exp0->AsInitial();
    const ExpInitial *nexp1 = exp1->AsInitial();
    TryCompareObjects(nexp0->GetTarget(), nexp1->GetTarget(), Exp);
    TryCompareObjects(nexp0->GetValueKind(), nexp1->GetValueKind(), Exp);
    break;
  }
  case EK_Val: {
    const ExpVal *nexp0 = exp0->AsVal();
    const ExpVal *nexp1 = exp1->AsVal();
    TryCompareObjects(nexp0->GetLvalue(), nexp1->GetLvalue(), Exp);
    TryCompareObjects(nexp0->GetValueKind(), nexp1->GetValueKind(), Exp);
    TryCompareValues(nexp0->GetPoint(), nexp1->GetPoint());
    TryCompareValues((int)nexp0->IsRelative(), (int)nexp1->IsRelative());
    break;
  }
  case EK_Frame: {
    const ExpFrame *nexp0 = exp0->AsFrame();
    const ExpFrame *nexp1 = exp1->AsFrame();
    TryCompareObjects(nexp0->GetValue(), nexp1->GetValue(), Exp);
    TryCompareValues(nexp0->GetFrameId(), nexp1->GetFrameId());
    break;
  }

  case EK_NullTest: {
    const ExpNullTest *nexp0 = exp0->AsNullTest();
    const ExpNullTest *nexp1 = exp1->AsNullTest();
    TryCompareObjects(nexp0->GetTarget(), nexp1->GetTarget(), Exp);
    break;
  }
  case EK_Bound: {
    const ExpBound *nexp0 = exp0->AsBound();
    const ExpBound *nexp1 = exp1->AsBound();
    TryCompareValues(nexp0->GetBoundKind(), nexp1->GetBoundKind());
    TryCompareObjects(nexp0->GetTarget(), nexp1->GetTarget(), Exp);
    TryCompareObjects(nexp0->GetStrideType(), nexp1->GetStrideType(), Type);
    break;
  }
  case EK_Directive: {
    const ExpDirective *nexp0 = exp0->AsDirective();
    const ExpDirective *nexp1 = exp1->AsDirective();
    TryCompareValues(nexp0->GetDirectiveKind(), nexp1->GetDirectiveKind());
    break;
  }
  case EK_Terminate: {
    const ExpTerminate *nexp0 = exp0->AsTerminate();
    const ExpTerminate *nexp1 = exp1->AsTerminate();
    TryCompareObjects(nexp0->GetTarget(), nexp1->GetTarget(), Exp);
    TryCompareObjects(nexp0->GetStrideType(), nexp1->GetStrideType(), Type);
    TryCompareObjects(nexp0->GetTerminateTest(),
                      nexp1->GetTerminateTest(), Exp);
    TryCompareObjects(nexp0->GetTerminateInt(),
                      nexp1->GetTerminateInt(), Exp);
    break;
  }
  case EK_GCSafe: {
    const ExpGCSafe *nexp0 = exp0->AsGCSafe();
    const ExpGCSafe *nexp1 = exp1->AsGCSafe();
    TryCompareObjects(nexp0->GetTarget(), nexp1->GetTarget(), Exp);
    break;
  }

  default:
    Assert(false);
  }

  return 0;
}

#define COPY_EXP(NAME)                                                  \
  case EK_ ## NAME: return new Exp ## NAME (*(const Exp ## NAME *) exp)

Exp* Exp::Copy(const Exp *exp)
{
  switch (exp->Kind()) {
    COPY_EXP(Empty);

    COPY_EXP(Var);
    COPY_EXP(Drf);
    COPY_EXP(Fld);
    COPY_EXP(Rfld);
    COPY_EXP(Index);
    COPY_EXP(String);
    COPY_EXP(Clobber);

    COPY_EXP(Int);
    COPY_EXP(Float);
    COPY_EXP(Unop);
    COPY_EXP(Binop);

    COPY_EXP(Exit);
    COPY_EXP(Initial);
    COPY_EXP(Val);
    COPY_EXP(Frame);

    COPY_EXP(NullTest);
    COPY_EXP(Bound);
    COPY_EXP(Directive);
    COPY_EXP(Terminate);
    COPY_EXP(GCSafe);

  default:
    Assert(false);
    return NULL;
  }
}

void Exp::Write(Buffer *buf, const Exp *exp)
{
  WriteOpenTag(buf, TAG_Exp);

  WriteTagUInt32(buf, TAG_Kind, exp->Kind());

  if (exp->Bits())
    WriteTagUInt32(buf, TAG_Width, exp->Bits());
  if (!exp->Sign())
    WriteTagEmpty(buf, TAG_ExpUnsigned);

  switch (exp->Kind()) {
  case EK_Empty: {
    break;
  }

  case EK_Var: {
    const ExpVar *nexp = exp->AsVar();
    Variable::Write(buf, nexp->GetVariable());
    break;
  }
  case EK_Drf: {
    const ExpDrf *nexp = exp->AsDrf();
    Exp::Write(buf, nexp->GetTarget());
    break;
  }
  case EK_Fld: {
    const ExpFld *nexp = exp->AsFld();
    Exp::Write(buf, nexp->GetTarget());
    Field::Write(buf, nexp->GetField());
    break;
  }
  case EK_Rfld: {
    const ExpRfld *nexp = exp->AsRfld();
    Exp::Write(buf, nexp->GetTarget());
    Field::Write(buf, nexp->GetField());
    break;
  }
  case EK_Index: {
    const ExpIndex *nexp = exp->AsIndex();
    Exp::Write(buf, nexp->GetTarget());
    Exp::Write(buf, nexp->GetIndex());
    Type::Write(buf, nexp->GetElementType());
    break;
  }
  case EK_String: {
    const ExpString *nexp = exp->AsString();
    Type *type = nexp->GetType();
    Assert(type);
    Type::Write(buf, type);
    DataString::Write(buf, nexp->GetString());
    break;
  }
  case EK_Clobber: {
    const ExpClobber *nexp = exp->AsClobber();
    Exp::Write(buf, nexp->GetCallee());
    Exp::Write(buf, nexp->GetOverwrite());
    if (nexp->GetValueKind())
      Exp::Write(buf, nexp->GetValueKind());
    WriteTagUInt32(buf, TAG_Index, nexp->GetPoint());
    if (nexp->GetLocation())
      Location::Write(buf, nexp->GetLocation());
    break;
  }

  case EK_Int: {
    const ExpInt *nexp = exp->AsInt();
    const char *val = nexp->GetValue();

    WriteString(buf, (const uint8_t*) val, strlen(val) + 1);
    break;
  }
  case EK_Float: {
    const ExpFloat *nexp = exp->AsFloat();
    const char *val = nexp->GetValue();

    WriteString(buf, (const uint8_t*) val, strlen(val) + 1);
    break;
  }
  case EK_Unop: {
    const ExpUnop *nexp = exp->AsUnop();
    WriteTagUInt32(buf, TAG_OpCode, nexp->GetUnopKind());
    Exp::Write(buf, nexp->GetOperand());
    break;
  }
  case EK_Binop: {
    const ExpBinop *nexp = exp->AsBinop();
    WriteTagUInt32(buf, TAG_OpCode, nexp->GetBinopKind());
    Exp::Write(buf, nexp->GetLeftOperand());
    Exp::Write(buf, nexp->GetRightOperand());
    if (nexp->GetStrideType())
      Type::Write(buf, nexp->GetStrideType());
    break;
  }

  case EK_Exit: {
    const ExpExit *nexp = exp->AsExit();
    Exp::Write(buf, nexp->GetTarget());
    if (nexp->GetValueKind())
      Exp::Write(buf, nexp->GetValueKind());
    break;
  }
  case EK_Initial: {
    const ExpInitial *nexp = exp->AsInitial();
    Exp::Write(buf, nexp->GetTarget());
    if (nexp->GetValueKind())
      Exp::Write(buf, nexp->GetValueKind());
    break;
  }
  case EK_Val: {
    const ExpVal *nexp = exp->AsVal();
    Exp::Write(buf, nexp->GetLvalue());
    if (nexp->GetValueKind())
      Exp::Write(buf, nexp->GetValueKind());
    WriteTagUInt32(buf, TAG_Index, nexp->GetPoint());
    WriteTagEmpty(buf, nexp->IsRelative() ? TAG_True : TAG_False);
    break;
  }
  case EK_Frame:
    Assert(false);

  case EK_NullTest: {
    const ExpNullTest *nexp = exp->AsNullTest();
    Exp::Write(buf, nexp->GetTarget());
    break;
  }
  case EK_Bound: {
    const ExpBound *nexp = exp->AsBound();
    WriteTagUInt32(buf, TAG_OpCode, nexp->GetBoundKind());
    Type::Write(buf, nexp->GetStrideType());
    if (Exp *target = nexp->GetTarget())
      Exp::Write(buf, target);
    break;
  }
  case EK_Directive: {
    const ExpDirective *nexp = exp->AsDirective();
    WriteTagUInt32(buf, TAG_OpCode, nexp->GetDirectiveKind());
    break;
  }
  case EK_Terminate: {
    const ExpTerminate *nexp = exp->AsTerminate();
    Type::Write(buf, nexp->GetStrideType());
    Exp::Write(buf, nexp->GetTerminateTest());
    Exp::Write(buf, nexp->GetTerminateInt());
    if (Exp *target = nexp->GetTarget())
      Exp::Write(buf, target);
    break;
  }
  case EK_GCSafe: {
    const ExpGCSafe *nexp = exp->AsGCSafe();
    if (Exp *target = nexp->GetTarget())
      Exp::Write(buf, target);

    // this should only show up during checking.
    Assert(!nexp->NeedsRoot());
    break;
  }

  default:
    Assert(false);
  }

  WriteCloseTag(buf, TAG_Exp);
}

Exp* Exp::Read(Buffer *buf)
{
  uint32_t kind = 0;
  uint32_t bits = 0;
  bool sign = true;

  uint32_t opcode = 0;
  uint32_t point = 0;
  Variable *var = NULL;
  Exp *exp0 = NULL;
  Exp *exp1 = NULL;
  Exp *exp2 = NULL;
  Field *field = NULL;
  Type *type = NULL;
  Location *loc = NULL;

  bool flag_true = false;
  bool flag_false = false;

  const uint8_t *str = NULL;
  size_t str_len = 0;

  Try(ReadOpenTag(buf, TAG_Exp));
  while (!ReadCloseTag(buf, TAG_Exp)) {
    switch (PeekOpenTag(buf)) {
    case TAG_Kind: {
      Try(!kind);
      Try(ReadTagUInt32(buf, TAG_Kind, &kind));
      break;
    }
    case TAG_Width: {
      Try(ReadTagUInt32(buf, TAG_Width, &bits));
      break;
    }
    case TAG_ExpUnsigned: {
      Try(ReadTagEmpty(buf, TAG_ExpUnsigned));
      sign = false;
      break;
    }
    case TAG_Exp: {
      if (exp0) {
        if (exp1) {
          Try(!exp2);
          exp2 = Exp::Read(buf);
        }
        else {
          exp1 = Exp::Read(buf);
        }
      }
      else {
        exp0 = Exp::Read(buf);
      }
      break;
    }
    case TAG_Variable: {
      Try(!var);
      var = Variable::Read(buf);
      break;
    }
    case TAG_Field: {
      Try(!field);
      field = Field::Read(buf);
      break;
    }
    case TAG_Type: {
      Try(!type);
      type = Type::Read(buf);
      break;
    }
    case TAG_String: {
      Try(!str);
      Try(ReadString(buf, &str, &str_len));
      break;
    }
    case TAG_OpCode: {
      Try(ReadTagUInt32(buf, TAG_OpCode, &opcode));
      break;
    }
    case TAG_Index: {
      Try(!point);
      Try(ReadTagUInt32(buf, TAG_Index, &point));
      break;
    }
    case TAG_Location: {
      Try(!loc);
      loc = Location::Read(buf);
      break;
    }
    case TAG_True: {
      flag_true = true;
      Try(ReadTagEmpty(buf, TAG_True));
      break;
    }
    case TAG_False: {
      flag_false = true;
      Try(ReadTagEmpty(buf, TAG_False));
      break;
    }
    default:
      Try(false);
    }
  }

  Exp *res = NULL;

  switch ((ExpKind)kind) {
  case EK_Empty:
    res = MakeEmpty();
    break;

  case EK_Var:
    res = MakeVar(var);
    break;
  case EK_Drf:
    res = MakeDrf(exp0);
    break;
  case EK_Fld:
    res = MakeFld(exp0, field);
    break;
  case EK_Rfld:
    res = MakeRfld(exp0, field);
    break;
  case EK_Index:
    res = MakeIndex(exp0, type, exp1);
    break;
  case EK_String:
    res = MakeString(type->AsArray(), DataString::Make(str, str_len));
    break;
  case EK_Clobber:
    res = MakeClobber(exp0, exp2, exp1, (PPoint) point, loc);
    break;

  case EK_Int:
    Try(str_len > 0 && str[str_len - 1] == 0);
    res = MakeIntStr((const char*) str);
    break;
  case EK_Float:
    Try(str_len > 0 && str[str_len - 1] == 0);
    res = MakeFloat((const char*) str);
    break;
  case EK_Unop:
    res = MakeUnop((UnopKind)opcode, exp0, bits, sign);
    break;
  case EK_Binop:
    res = MakeBinop((BinopKind)opcode, exp0, exp1, type, bits, sign);
    break;

  case EK_Exit:
    res = MakeExit(exp0, exp1);
    break;
  case EK_Initial:
    res = MakeInitial(exp0, exp1);
    break;
  case EK_Val:
    Assert(flag_true != flag_false);
    res = MakeVal(exp0, exp1, (PPoint) point, flag_true);
    break;
  case EK_Frame:
    Assert(false);

  case EK_NullTest:
    res = MakeNullTest(exp0);
    break;
  case EK_Bound:
    res = MakeBound((BoundKind)opcode, exp0, type);
    break;
  case EK_Directive:
    res = MakeDirective((DirectiveKind)opcode);
    break;
  case EK_Terminate:
    Try(exp1);
    res = MakeTerminate(exp2, type, exp0, exp1->AsInt());
    break;
  case EK_GCSafe:
    res = MakeGCSafe(exp0, false);
    break;

  default:
    Assert(false);
  }

  Assert(res);
  return res;
}

/////////////////////////////////////////////////////////////////////
// Exp construction utility
/////////////////////////////////////////////////////////////////////

void FillExpInfo(Exp *exp, FullExpInfo *info_array, size_t *info_count)
{
  FullExpInfo &info = info_array[0];

  info.Set(exp);
  size_t count = 1;
  size_t new_count;

  // for each applicable reversible binop at exp, exp->left, or exp->right,
  // we will double the number of permutations of the information.

  // (a + b) * (c - d)

  // permute the top level expression if possible.

  if (BinopKind new_kind = ReverseBinop(info.i.b_kind)) {
    if (info.li.exp != info.ri.exp) {
      Assert(count == 1);
      FullExpInfo &new_info = info_array[1];
      new_info = info;
      new_info.i.b_kind = new_kind;
      new_info.li.Swap(new_info.ri);
      new_info.lli.Swap(new_info.rli);
      new_info.lri.Swap(new_info.rri);
      count = 2;
    }
  }

  // (a + b) * (c - d)
  // (c - d) * (a + b)

  // permute the left expressions of the result if possible. these could be
  // either the original exp->left or exp->right (only if exp is permutable).

  new_count = count;

  for (size_t ind = 0; ind < count; ind++) {
    const FullExpInfo &info = info_array[ind];
    if (BinopKind new_kind = ReverseBinop(info.li.b_kind)) {
      if (info.lli.exp != info.lri.exp) {
        FullExpInfo &new_info = info_array[new_count++];
        new_info = info;
        new_info.li.b_kind = new_kind;
        new_info.lli.Swap(new_info.lri);
      }
    }
  }

  count = new_count;

  // (a + b) * (c - d)
  // (b + a) * (c - d)
  // (c - d) * (a + b)

  // permute the right expressions of the result if possible. again, these
  // could be either the original exp->left or exp->right.

  new_count = count;

  for (size_t ind = 0; ind < count; ind++) {
    const FullExpInfo &info = info_array[ind];
    if (BinopKind new_kind = ReverseBinop(info.ri.b_kind)) {
      if (info.rli.exp != info.rri.exp) {
        FullExpInfo &new_info = info_array[new_count++];
        new_info = info;
        new_info.ri.b_kind = new_kind;
        new_info.rli.Swap(new_info.rri);
      }
    }
  }

  count = new_count;

  // (a + b) * (c - d)
  // (b + a) * (c - d)
  // (c - d) * (a + b)
  // (c - d) * (b + a)

  *info_count = count;
}

// get a normalized type for an expression, if different from stride_type.
static inline Type* NormalizeType(Type *type)
{
  // convert void to signed char.
  if (type->IsVoid())
    return Type::MakeInt(1, true);

  // convert unsigned integers to signed.
  if (type->IsInt() && !type->IsSigned())
    return Type::MakeInt(type->Width(), true);

  // convert all pointers to void*.
  if (TypePointer *ntype = type->IfPointer()) {
    if (!ntype->GetTargetType()->IsVoid()) {
      Type *void_type = Type::MakeVoid();
      return Type::MakePointer(void_type, type->Width());
    }
  }

  return NULL;
}

// is type equivalent to normal_type, modulo normalization?
// normal_type must already be normalized.
static inline bool IsCompatibleNormalizedType(Type *type, Type *normal_type)
{
  if (type == normal_type)
    return true;

  if (Type *new_type = NormalizeType(type)) {
    bool equals = (new_type == normal_type);
    return equals;
  }

  return false;
}

/////////////////////////////////////////////////////////////////////
// Exp construction
/////////////////////////////////////////////////////////////////////

// if check_equivalent is set then equivalence checking will be performed
// between the two values if enabled. check_equivalent should be false only
// for simplifications which improve information that the solver did not
// understand in the first place (PlusPI, MinusPI, introduce Rfld, etc.).
static inline Exp* SimplifyExp(Exp *exp, Exp *new_exp,
                               bool check_equivalent = true)
{
  if (check_equivalent && g_callback_ExpSimplify)
    g_callback_ExpSimplify(exp, new_exp);
  return new_exp;
}

Exp* Exp::MakeEmpty()
{
  ExpEmpty xexp;
  return g_table.Lookup(xexp);
}

Exp* Exp::MakeVar(Variable *var)
{
  ExpVar xexp(var);
  return g_table.Lookup(xexp);
}

Exp* Exp::MakeVar(BlockId *id, VarKind kind,
                  String *name, size_t index, String *source_name)
{
  Variable *var = Variable::Make(id, kind, name, index, source_name);
  ExpVar xexp(var);
  return g_table.Lookup(xexp);
}

Exp* Exp::MakeDrf(Exp *target)
{
  ExpDrf xexp(target);
  return g_table.Lookup(xexp);
}

Exp* Exp::MakeFld(Exp *target, Field *field)
{
  ExpFld xexp(target, field);
  Exp *exp = g_table.Lookup(xexp);

  // input:  Fld(Rfld(exp,field),field)
  // output: exp

  if (ExpRfld *ntarget = target->IfRfld()) {
    if (field == ntarget->GetField()) {
      Exp *inner_target = ntarget->GetTarget();
      return SimplifyExp(exp, inner_target, false);
    }
  }

  return exp;
}

Exp* Exp::MakeRfld(Exp *target, Field *field)
{
  ExpRfld xexp(target, field);
  Exp *exp = g_table.Lookup(xexp);

  // input:  Rfld(Fld(exp,field),field)
  // output: exp

  if (ExpFld *ntarget = target->IfFld()) {
    if (field == ntarget->GetField()) {
      Exp *inner_target = ntarget->GetTarget();
      return SimplifyExp(exp, inner_target, false);
    }
  }

  return exp;
}

// get the width of an int or pointer type, 0 otherwise.
// these types do not have to go to a database for their widths.
static inline size_t SimpleWidth(Type *type)
{
  if (type->IsInt() || type->IsPointer())
    return type->Width();
  return 0;
}

Exp* Exp::MakeIndex(Exp *target, Type *element_type, Exp *index)
{
  ExpIndex xexp(target, element_type, index);
  Exp *exp = g_table.Lookup(xexp);

  // input:  Index(Index(exp0, type, exp1), type, exp2)
  // output: Index(exp0, type, exp1 + exp2)

  if (ExpIndex *ntarget = target->IfIndex()) {
    Type *target_type = ntarget->GetElementType();

    // allow if the widths are equal, for integer/pointer types.
    // we will discard the target's type.

    if (element_type == target_type ||
        (SimpleWidth(element_type) &&
         SimpleWidth(element_type) == SimpleWidth(target_type))) {

      Exp *inner_target = ntarget->GetTarget();
      Exp *inner_index = ntarget->GetIndex();

      Exp *new_index = MakeBinop(B_Plus, index, inner_index);
      Exp *new_exp = MakeIndex(inner_target, element_type, new_index);
      return SimplifyExp(exp, new_exp, false);
    }
  }

  // input:  Index(n, type, exp)
  // output: n + exp * sizeof(type)

  if (target->IsInt()) {
    if (size_t width = SimpleWidth(element_type)) {
      Exp *width_exp = MakeInt(width);

      Exp *mult_exp = MakeBinop(B_Mult, index, width_exp);
      Exp *new_exp = MakeBinop(B_Plus, target, mult_exp);
      return SimplifyExp(exp, new_exp, false);
    }
  }

  return exp;
}

Exp* Exp::MakeString(TypeArray *type, DataString *str)
{
  ExpString xexp(type, str);
  return g_table.Lookup(xexp);
}

Exp* Exp::MakeString(String *str)
{
  const char *data = str->Value();
  size_t len = strlen(data);

  Type *elem_type = Type::MakeInt(1, true);
  TypeArray *type = Type::MakeArray(elem_type, len + 1);

  DataString *nstr = DataString::Make((const uint8_t*) data, len + 1);

  ExpString xexp(type, nstr);
  return g_table.Lookup(xexp);
}

ExpClobber* Exp::MakeClobber(Exp *callee, Exp *value_kind, Exp *overwrite,
                             PPoint point, Location *location)
{
  ExpClobber xexp(callee, value_kind, overwrite, point, location);
  return g_table.Lookup(xexp)->AsClobber();
}

ExpInt* Exp::MakeIntMpz(const mpz_t value, size_t bits, bool sign)
{
  if (bits == 0)
    Assert(sign);

  static Buffer buf;

  // for doing coercions, we need bitmasks to take the bitwise and with
  // and get the lower N bits of the input value. only support coercions
  // for 8, 16, 32, and 64 bit quantities, and only construct the masks once.
  static mpz_t mask8, mask16, mask32, mask64;

  // bitwise complement of the above masks.
  static mpz_t comp8, comp16, comp32, comp64;

  static bool init_mask = false;
  if (!init_mask) {
    init_mask = true;

    mpz_init(mask8);
    for (size_t i = 0; i < 8; i++) mpz_setbit(mask8, i);

    mpz_init(mask16);
    for (size_t i = 0; i < 16; i++) mpz_setbit(mask16, i);

    mpz_init(mask32);
    for (size_t i = 0; i < 32; i++) mpz_setbit(mask32, i);

    mpz_init(mask64);
    for (size_t i = 0; i < 64; i++) mpz_setbit(mask64, i);

    mpz_init(comp8);
    mpz_com(comp8, mask8);

    mpz_init(comp16);
    mpz_com(comp16, mask16);

    mpz_init(comp32);
    mpz_com(comp32, mask32);

    mpz_init(comp64);
    mpz_com(comp64, mask64);
  }

  if (bits) {
    // need to do a coercion, find the appropriate mask to use.
    mpz_t mask, comp;
    if (bits == 8) {
      mpz_init_set(mask, mask8);
      mpz_init_set(comp, comp8);
    }
    else if (bits == 16) {
      mpz_init_set(mask, mask16);
      mpz_init_set(comp, comp16);
    }
    else if (bits == 32) {
      mpz_init_set(mask, mask32);
      mpz_init_set(comp, comp32);
    }
    else if (bits == 64) {
      mpz_init_set(mask, mask64);
      mpz_init_set(comp, comp64);
    }
    else Assert(false);

    // get the result of the bitwise and with the mask.
    mpz_t mpz;
    mpz_init(mpz);
    mpz_and(mpz, value, mask);

    // this had better be non-negative.
    Assert(mpz_cmp_si(mpz, 0) >= 0);

    // check if we need to compute the negation. this occurs if the
    // result is signed and the high bit in the mpz is set.
    if (sign && mpz_tstbit(mpz, bits - 1)) {
      mpz_ior(mpz, mpz, comp);
      Assert(mpz_cmp_si(mpz, 0) < 0);
    }

    IntToString(&buf, mpz);
    mpz_clear(mpz);
    mpz_clear(mask);
    mpz_clear(comp);
  }
  else {
    Assert(sign);
    IntToString(&buf, value);
  }

  ExpInt xexp((const char*) buf.base);
  ExpInt *res = g_table.Lookup(xexp)->AsInt();

  buf.Reset();
  return res;
}

ExpInt* Exp::MakeIntStr(const char *value)
{
  ExpInt xexp(value);
  return g_table.Lookup(xexp)->AsInt();
}

ExpInt* Exp::MakeInt(long value)
{
  static Buffer buf;

  mpz_t mpz;
  mpz_init_set_si(mpz, value);

  IntToString(&buf, mpz);
  ExpInt xexp((const char*) buf.base);
  ExpInt *res = g_table.Lookup(xexp)->AsInt();

  mpz_clear(mpz);
  buf.Reset();
  return res;
}

Exp* Exp::MakeFloat(const char *value)
{
  ExpFloat xexp(value);
  return g_table.Lookup(xexp);
}

Exp* Exp::MakeUnop(UnopKind unop_kind, Exp *op, size_t bits, bool sign)
{
  ExpUnop xexp(unop_kind, op, bits, sign);
  Exp *exp = g_table.Lookup(xexp);

  FullExpInfo info;
  info.Set(exp);

  const ExpInfo &i = info.i;
  const ExpInfo &li = info.li;
  const ExpInfo &lli = info.lli;
  const ExpInfo &lri = info.lri;

  // constant fold unops.

  if (li.has_value) {
    mpz_t res;
    mpz_init(res);

    ConstFoldUnop(i.u_kind, li.value, res);
    Exp *new_exp = MakeIntMpz(res, bits, sign);
    mpz_clear(res);

    return SimplifyExp(exp, new_exp, false);
  }

  // input:  !!exp
  // output: exp != 0

  // note that this is *not* equivalent to exp itself.
  // !!x is a common way to write 'x != 0' in C/C++. if MakeNonZeroBit
  // is called after this the '!= 0' part will go away.

  if (i.u_kind == U_LogicalNot && li.u_kind == U_LogicalNot) {
    Exp *zero_op = MakeInt(0);
    Exp *new_exp = MakeBinop(B_NotEqual, lli.exp, zero_op);
    return SimplifyExp(exp, new_exp);
  }

  // input:  -(-exp)
  // output: exp

  if (i.u_kind == U_Neg && li.u_kind == U_Neg)
    return SimplifyExp(exp, lli.exp);

  // input:  -(exp0 - exp1)
  // output: exp1 - exp0

  if (i.u_kind == U_Neg && li.b_kind == B_Minus) {
    Exp *new_exp = MakeBinop(B_Minus, lri.exp, lli.exp,
                             NULL, bits, sign);
    return SimplifyExp(exp, new_exp);
  }

  // stopgap: remove all coercion unops. TODO: need to settle this
  // and make sure coercions never appear in an lvalue context.
  if (i.u_kind == U_Coerce)
    return SimplifyExp(exp, li.exp);

  /*

  // simplification forms after this are for complete arithmetic.
  if (bits)
    return exp;

  // remove any coercion unops.

  if (i.u_kind == U_Coerce)
    return SimplifyExp(exp, li.exp);

  */

  return exp;
}

// for an expression Fld(Fld(0,F),G) (i.e. (0).F.G), return the fields <G,F>
// through field_chain. return whether the expression matches this format.
static bool GetFieldChain(Exp *exp, Vector<Field*> *field_chain)
{
  Assert(field_chain->Empty());
  Exp *cur_exp = exp;

  while (true) {
    if (ExpInt *nexp = cur_exp->IfInt()) {
      long val;
      if (nexp->GetInt(&val) && val == 0)
        return true;

      field_chain->Clear();
      return false;
    }

    if (ExpFld *nexp = cur_exp->IfFld()) {
      field_chain->PushBack(nexp->GetField());
      cur_exp = nexp->GetTarget();
      continue;
    }

    field_chain->Clear();
    return false;
  }
}

Exp* Exp::MakeBinop(BinopKind binop_kind,
                    Exp *left_op, Exp *right_op,
                    Type *stride_type, size_t bits, bool sign)
{
  ExpBinop xexp(binop_kind, left_op, right_op, stride_type, bits, sign);
  Exp *exp = g_table.Lookup(xexp);

  FullExpInfo info;
  info.Set(exp);

  const ExpInfo &i = info.i;
  const ExpInfo &li = info.li;
  const ExpInfo &ri = info.ri;

  // input:  (exp -p 0.field_chain)
  // output: Rfld(exp, reverse_field_chain))

  bool is_char_type = false;
  if (stride_type && stride_type->IsInt())
    is_char_type = (stride_type->Width() == 1);

  if (i.b_kind == B_MinusPI && is_char_type &&
      li.exp->IsLvalue() && ri.exp->IsLvalue()) {
    Vector<Field*> reverse_field_chain;
    if (GetFieldChain(ri.exp, &reverse_field_chain)) {
      Assert(reverse_field_chain.Size());

      Exp *cur_exp = li.exp;

      // generate the Rfld expressions so that we end up reversing the
      // order from the original field chain:
      //   T - Fld(Fld(0,F),G)  ==>  Rfld(Rfld(T,G),F)
      for (size_t find = 0; find < reverse_field_chain.Size(); find++) {
        Field *field = reverse_field_chain[find];
        Exp *new_exp = MakeRfld(cur_exp, field);
        cur_exp = new_exp;
      }

      return SimplifyExp(exp, cur_exp, false);
    }
  }

  // normalize the stride type if necessary.

  if (stride_type) {
    if (Type *new_stride_type = NormalizeType(stride_type)) {
      Exp *new_exp = MakeBinop(i.b_kind, li.exp, ri.exp, new_stride_type);
      return SimplifyExp(exp, new_exp);
    }
  }

  // input:  (exp0 +p exp1)
  // output: Index(exp0, exp1)

  // input:  (exp0 -p exp1)
  // output: Index(exp0, -exp1)

  if (i.b_kind == B_PlusPI || i.b_kind == B_MinusPI) {
    Assert(stride_type);

    Exp *index;
    if (i.b_kind == B_PlusPI)
      index = ri.exp;
    else
      index = MakeUnop(U_Neg, ri.exp);

    Exp *new_exp = MakeIndex(li.exp, stride_type, index);
    return SimplifyExp(exp, new_exp, false);
  }

  // input:  (Index(exp0,exp1) -pp exp2)
  // output: exp1 + (exp0 -pp exp2)

  if (i.b_kind == B_MinusPP && li.exp->IsIndex()) {
    ExpIndex *nleft = li.exp->AsIndex();
    if (IsCompatibleNormalizedType(nleft->GetElementType(), stride_type)) {
      Exp *target = nleft->GetTarget();
      Exp *index = nleft->GetIndex();

      Exp *new_minus = MakeBinop(B_MinusPP, target, ri.exp, stride_type);
      Exp *new_exp = MakeBinop(B_Plus, index, new_minus);
      return SimplifyExp(exp, new_exp);
    }
  }

  // input:  (exp0 -pp Index(exp1,exp2))
  // output: (exp0 -pp exp1) - exp2

  if (i.b_kind == B_MinusPP && ri.exp->IsIndex()) {
    ExpIndex *nright = ri.exp->AsIndex();
    if (IsCompatibleNormalizedType(nright->GetElementType(), stride_type)) {
      Exp *target = nright->GetTarget();
      Exp *index = nright->GetIndex();

      Exp *new_minus = MakeBinop(B_MinusPP, li.exp, target, stride_type);
      Exp *new_exp = MakeBinop(B_Minus, new_minus, index);
      return SimplifyExp(exp, new_exp);
    }
  }

  // constant fold binops.

  if (li.has_value && ri.has_value) {
    mpz_t res;
    mpz_init(res);

    ConstFoldBinop(i.b_kind, li.value, ri.value, res);
    Exp *new_exp = MakeIntMpz(res, bits, sign);

    mpz_clear(res);
    return SimplifyExp(exp, new_exp, false);
  }

  // simplification forms which may use commutativity.

  FullExpInfo info_array[8];
  size_t info_count;

  FillExpInfo(exp, info_array, &info_count);

  for (size_t ind = 0; ind < info_count; ind++) {

    // replace the earlier bindings for these values.
    const FullExpInfo &fi = info_array[ind];
    const ExpInfo &i = fi.i;
    const ExpInfo &li = fi.li;
    const ExpInfo &ri = fi.ri;
    const ExpInfo &lli = fi.lli;
    const ExpInfo &lri = fi.lri;
    const ExpInfo &rli = fi.rli;
    const ExpInfo &rri = fi.rri;

    // input:  exp +/- 0
    // output: exp

    if ((i.b_kind == B_Plus || i.b_kind == B_Minus) &&
        ri.has_value && mpz_cmp_si(ri.value, 0) == 0) {
      return SimplifyExp(exp, li.exp);
    }

    // input:  exp * 1
    // output: exp

    if (i.b_kind == B_Mult && ri.has_value && mpz_cmp_si(ri.value, 1) == 0)
      return SimplifyExp(exp, li.exp);

    // input:  0 - exp
    // output: -exp

    if (i.b_kind == B_Minus &&
        li.has_value && mpz_cmp_si(li.value, 0) == 0) {
      Exp *new_exp = MakeUnop(U_Neg, ri.exp, bits, sign);
      return SimplifyExp(exp, new_exp);
    }

    // input:  exp - exp
    //    or:  exp != exp
    //    or:  exp < exp
    // output: 0

    if (li.exp == ri.exp &&
        (i.b_kind == B_Minus || i.b_kind == B_MinusPP ||
         i.b_kind == B_NotEqual ||
         i.b_kind == B_LessThan || i.b_kind == B_LessThanP)) {
      Exp *new_exp = MakeInt(0);
      return SimplifyExp(exp, new_exp);
    }

    // input:  exp == exp
    //    or:  exp <= exp
    // output: 1

    if (li.exp == ri.exp &&
        (i.b_kind == B_Equal ||
         i.b_kind == B_LessEqual || i.b_kind == B_LessEqualP)) {
      Exp *new_exp = MakeInt(1);
      return SimplifyExp(exp, new_exp);
    }

    // input:  exp !=p n
    // output: !null(exp)

    if (i.b_kind == B_NotEqualP && ri.has_value) {
      Exp *null_exp = MakeNullTest(li.exp);
      Exp *new_exp = MakeUnop(U_LogicalNot, null_exp);
      return SimplifyExp(exp, new_exp, false);
    }

    // input:  exp ==p n
    // output: null(exp)

    if (i.b_kind == B_EqualP && ri.has_value) {
      Exp *new_exp = MakeNullTest(li.exp);
      return SimplifyExp(exp, new_exp, false);
    }

    // input:  exp0 +/- -exp1
    // output: exp0 -/+ exp1

    if ((i.b_kind == B_Plus || i.b_kind == B_Minus) && ri.u_kind == U_Neg) {
      BinopKind new_kind = (i.b_kind == B_Plus ? B_Minus : B_Plus);
      Exp *new_exp = MakeBinop(new_kind, li.exp, rli.exp, NULL, bits, sign);
      return SimplifyExp(exp, new_exp);
    }

    // input:  exp0 +/- -n
    // output: exp0 -/+ n

    if ((i.b_kind == B_Plus || i.b_kind == B_Minus) &&
        (ri.has_value && mpz_cmp_si(ri.value, 0) < 0)) {
      BinopKind new_kind = (i.b_kind == B_Plus ? B_Minus : B_Plus);
      Exp *op_exp = MakeUnop(U_Neg, ri.exp);
      Exp *new_exp = MakeBinop(new_kind, li.exp, op_exp, NULL, bits, sign);
      return SimplifyExp(exp, new_exp);
    }

    // input:  (exp +/- n0) +/- n1
    // output: exp + (+/- n0 +/- n1)

    if ((i.b_kind == B_Plus || i.b_kind == B_Minus) &&
        (li.b_kind == B_Plus || li.b_kind == B_Minus) &&
        lri.has_value && ri.has_value) {
      Exp *const_left = lri.exp;
      if (li.b_kind == B_Minus)
        const_left = MakeUnop(U_Neg, const_left);
      Exp *right = MakeBinop(i.b_kind, const_left, ri.exp);
      Exp *new_exp = MakeBinop(B_Plus, lli.exp, right, NULL, bits, sign);
      return SimplifyExp(exp, new_exp);
    }

    // input:  (exp * n0) * n1
    // output: exp * (n0 * n1)

    if (i.b_kind == B_Mult && li.b_kind == B_Mult &&
        lri.has_value && ri.has_value) {
      Exp *right = MakeBinop(B_Mult, lri.exp, ri.exp);
      Exp *new_exp = MakeBinop(B_Mult, lli.exp, right, NULL, bits, sign);
      return SimplifyExp(exp, new_exp);
    }

    // input:  n0 - (exp +/- n1)
    // output: (n0 -/+ n1) - exp

    if (i.b_kind == B_Minus &&
        (ri.b_kind == B_Plus || ri.b_kind == B_Minus) &&
        li.has_value && rri.has_value) {
      BinopKind left_kind = (ri.b_kind == B_Minus ? B_Plus : B_Minus);
      Exp *left = MakeBinop(left_kind, li.exp, rri.exp);
      Exp *new_exp = MakeBinop(B_Minus, left, rli.exp, NULL, bits, sign);
      return SimplifyExp(exp, new_exp);
    }

    // input:  n0 - (n1 - exp)
    // output: (n0 - n1) + exp

    if (i.b_kind == B_Minus && ri.b_kind == B_Minus &&
        li.has_value && rli.has_value) {
      Exp *left = MakeBinop(B_Minus, li.exp, rli.exp);
      Exp *new_exp = MakeBinop(B_Plus, left, rri.exp, NULL, bits, sign);
      return SimplifyExp(exp, new_exp);
    }

    // move constants towards the root of the expression to facilitate
    // the above constant folding.
    // input:  (exp0 +/- n) +/- exp1
    // output: (exp0 +/- exp1) +/- n

    if ((i.b_kind == B_Plus || i.b_kind == B_Minus) &&
        (li.b_kind == B_Plus || li.b_kind == B_Minus) && lri.has_value) {
      Assert(!ri.has_value);
      Exp *left = MakeBinop(i.b_kind, lli.exp, ri.exp);
      Exp *new_exp = MakeBinop(li.b_kind, left, lri.exp, NULL, bits, sign);
      return SimplifyExp(exp, new_exp);
    }

    // input:  (exp0 + exp1) - exp1
    // output: exp0

    if (i.b_kind == B_Minus && li.b_kind == B_Plus && lri.exp == ri.exp)
      return SimplifyExp(exp, lli.exp);

    // input:  (exp0 - exp1) + exp1
    // output: exp0

    if (i.b_kind == B_Plus && li.b_kind == B_Minus && lri.exp == ri.exp)
      return SimplifyExp(exp, lli.exp);

    // input:  (n * exp0) op (n * exp1)  for op in {+,-}
    // output: n * (exp0 op exp1)

    if ((i.b_kind == B_Plus || i.b_kind == B_Minus) &&
        li.b_kind == B_Mult && ri.b_kind == B_Mult &&
        lli.has_value && rli.has_value &&
        mpz_cmp(lli.value, rli.value) == 0) {
      Exp *base_exp = MakeBinop(i.b_kind, lri.exp, rri.exp);
      Exp *new_exp = MakeBinop(B_Mult, lli.exp, base_exp, NULL, bits, sign);
      return SimplifyExp(exp, new_exp);
    }

    // input:  n0 * (exp op n1)  for op in {+,-}
    // output: n0 * exp op (n0 * n1)

    if (i.b_kind == B_Mult && (ri.b_kind == B_Plus || ri.b_kind == B_Minus) &&
        li.has_value && rri.has_value) {
      Exp *left_exp = MakeBinop(B_Mult, li.exp, rli.exp);
      Exp *right_exp = MakeBinop(B_Mult, li.exp, rri.exp);
      Exp *new_exp = MakeBinop(ri.b_kind, left_exp, right_exp,
                               NULL, bits, sign);
      return SimplifyExp(exp, new_exp);
    }

    // TODO: disabled. this introduces new nonlinear function applications
    // and can lead to infinite recursion when generating constraints for
    // these applications.
    /*
    // input:  exp0 + (exp0 * exp1)  for non-constant exp0
    // output: exp0 * (exp1 + 1)

    if (i.b_kind == B_Plus && ri.b_kind == B_Mult &&
        li.exp == rli.exp && !li.has_value) {
      Exp *one = MakeInt(1);
      Exp *right = MakeBinop(B_Plus, rri.exp, one);
      Exp *new_exp = MakeBinop(B_Mult, li.exp, right, NULL, bits, sign);
      return SimplifyExp(exp, new_exp);
    }
    */

    // input:  exp < 1
    // output: exp <= 0

    if (i.b_kind == B_LessThan &&
        ri.has_value && mpz_cmp_si(ri.value,1) == 0) {
      Exp *right = MakeInt(0);
      Exp *new_exp = MakeBinop(B_LessEqual, li.exp, right);
      return SimplifyExp(exp, new_exp);
    }

    // input:  -1 < exp
    // output: 0 <= exp

    if (i.b_kind == B_LessThan &&
        li.has_value && mpz_cmp_si(li.value,-1) == 0) {
      Exp *left = MakeInt(0);
      Exp *new_exp = MakeBinop(B_LessEqual, left, ri.exp);
      return SimplifyExp(exp, new_exp);
    }

    // input:  exp0 cmp exp1[-exp2]
    // output: exp0[exp2] cmp exp1

    if (IsCompareBinop(i.b_kind) && stride_type && ri.element_type &&
        (rri.u_kind == U_Neg ||
         (rri.has_value && mpz_cmp_si(rri.value, 0) < 0))) {
      Exp *new_index = MakeUnop(U_Neg, rri.exp);
      Exp *left = MakeIndex(li.exp, ri.element_type, new_index);
      Exp *new_exp = MakeBinop(i.b_kind, left, rli.exp, stride_type);
      return SimplifyExp(exp, new_exp);
    }

    // input:  exp0[1] <= exp1
    // output: exp0 < exp1

    if (i.b_kind == B_LessEqualP && stride_type && li.element_type &&
        li.exp->IsCompatibleStrideType(stride_type) &&
        lri.has_value && mpz_cmp_si(lri.value, 1) == 0) {
      Exp *new_exp = MakeBinop(B_LessThanP, lli.exp, ri.exp, stride_type);
      return SimplifyExp(exp, new_exp);
    }

    // input:  exp0 < exp1[1]
    // output: exp0 <= exp1

    if (i.b_kind == B_LessThanP && stride_type && ri.element_type &&
        ri.exp->IsCompatibleStrideType(stride_type) &&
        rri.has_value && mpz_cmp_si(rri.value, 1) == 0) {
      Exp *new_exp = MakeBinop(B_LessEqualP, li.exp, rli.exp, stride_type);
      return SimplifyExp(exp, new_exp);
    }

    // input:  exp0 cmp exp0[exp1]
    // output: 0 cmp exp1

    if ((i.b_kind == B_LessThanP || i.b_kind == B_LessEqualP) &&
        li.exp == rli.exp && stride_type && ri.element_type &&
        ri.exp->IsCompatibleStrideType(stride_type)) {
      Exp *left = MakeInt(0);
      BinopKind binop = (i.b_kind == B_LessThanP) ? B_LessThan : B_LessEqual;
      Exp *new_exp = MakeBinop(binop, left, rri.exp);
      return SimplifyExp(exp, new_exp);
    }

    // input: exp / 1
    // output: exp

    if ((i.b_kind == B_Div || i.b_kind == B_DivExact) &&
        ri.has_value && mpz_cmp_si(ri.value, 1) == 0) {
      return SimplifyExp(exp, li.exp);
    }

    // input:  (exp0 -pp exp1) cmp bound/term(exp1)
    // output: 0 cmp bound/term(exp0)

    if (IsCompareBinop(i.b_kind) && !stride_type && li.b_kind == B_MinusPP &&
        (ri.exp->IsBound() || ri.exp->IsTerminate()) &&
        ri.exp->GetLvalTarget() == lri.exp &&
        ri.exp->IsCompatibleStrideType(li.b_stride_type)) {
      Exp *left = MakeInt(0);
      Exp *right = ri.exp->ReplaceLvalTarget(lli.exp);
      Exp *new_exp = MakeBinop(i.b_kind, left, right);
      return SimplifyExp(exp, new_exp);
    }

    // simplifications after this point are only correct under complete
    // (non-modular) arithmetic, and the bits of subexpressions need
    // to be tested. the +/-/* binops have the same properties under
    // modular arithmetic as under complete arithmetic, so the simplifications
    // we perform for these are the same either way. other binops,
    // particularly comparisons and division, have different properties
    // and we usually can't simplify them under modular arithmetic.

    if (i.bits != 0 || li.bits != 0 || ri.bits != 0)
      continue;

    // input:  (n * exp0) cmp (n * exp1)  where n > 0
    // output: exp0 cmp exp1

    if (IsCompareBinop(i.b_kind) && !stride_type &&
        li.b_kind == B_Mult && ri.b_kind == B_Mult &&
        lli.has_value && rli.has_value &&
        mpz_cmp(lli.value, rli.value) == 0 &&
        mpz_cmp_si(lli.value, 0) > 0) {
      Exp *new_exp = MakeBinop(i.b_kind, lri.exp, rri.exp);
      return SimplifyExp(exp, new_exp);
    }

    // input:  n0 cmp (exp +/- n1)
    // output: n0 -/+ n1 cmp exp

    if (IsCompareBinop(i.b_kind) && !stride_type &&
        li.has_value && rri.has_value &&
        (ri.b_kind == B_Plus || ri.b_kind == B_Minus)) {
      BinopKind binop = (ri.b_kind == B_Plus) ? B_Minus : B_Plus;
      Exp *new_left = MakeBinop(binop, li.exp, rri.exp);
      Exp *new_exp = MakeBinop(i.b_kind, new_left, rli.exp);
      return SimplifyExp(exp, new_exp);
    }

    // input:  (exp0 +/- exp) cmp (exp1 +/- exp)
    // output: exp0 cmp exp1

    if (IsCompareBinop(i.b_kind) &&
        (li.b_kind == B_Plus || li.b_kind == B_Minus) &&
        ri.b_kind == li.b_kind && lri.exp == rri.exp) {
      Exp *new_exp = MakeBinop(i.b_kind, lli.exp, rli.exp, stride_type);
      return SimplifyExp(exp, new_exp);
    }

    // input:  exp0 cmp exp0 +/- exp1
    // output: 0 cmp +/- exp1

    if (IsCompareBinop(i.b_kind) &&
        (ri.b_kind == B_Plus || ri.b_kind == B_Minus) &&
        li.exp == rli.exp) {
      BinopKind compare_kind = NonPointerBinop(i.b_kind);

      Exp *right = rri.exp;
      if (ri.b_kind == B_Minus)
        right = MakeUnop(U_Neg, rri.exp);

      Exp *left = MakeInt(0);
      Exp *new_exp = MakeBinop(compare_kind, left, right);
      return SimplifyExp(exp, new_exp);
    }

    // input:  exp0 cmp (exp1 - exp2)
    // output: exp0 + exp2 cmp exp1

    if (IsCompareBinop(i.b_kind) && !stride_type && ri.b_kind == B_Minus) {
      Exp *left = MakeBinop(B_Plus, li.exp, rri.exp);
      Exp *new_exp = MakeBinop(i.b_kind, left, rli.exp);
      return SimplifyExp(exp, new_exp);
    }

    // input:  -exp0 cmp exp1
    // output: 0 cmp exp0 + exp1

    if (IsCompareBinop(i.b_kind) && !stride_type &&
        li.u_kind == U_Neg) {
      Exp *left = MakeInt(0);
      Exp *right = MakeBinop(B_Plus, lli.exp, ri.exp);
      Exp *new_exp = MakeBinop(i.b_kind, left, right);
      return SimplifyExp(exp, new_exp);
    }

    // input:  exp0 < exp1 + 1
    // output: exp0 <= exp1

    if (i.b_kind == B_LessThan && ri.b_kind == B_Plus &&
        rri.has_value && mpz_cmp_si(rri.value, 1) == 0) {
      Exp *new_exp = MakeBinop(B_LessEqual, li.exp, rli.exp);
      return SimplifyExp(exp, new_exp);
    }

    // input:  (exp0 / n) < exp1  (for n > 0)
    // output: exp0 < exp1 * n

    if (i.b_kind == B_LessThan &&
        (li.b_kind == B_Div || li.b_kind == B_DivExact) &&
        lri.has_value && mpz_cmp_si(lri.value, 0) > 0) {
      Exp *right = MakeBinop(B_Mult, lri.exp, ri.exp);
      Exp *new_exp = MakeBinop(i.b_kind, lli.exp, right);
      return SimplifyExp(exp, new_exp);
    }

    // input:  (exp0 * exp1) / exp1
    // output: exp0

    if ((i.b_kind == B_Div || i.b_kind == B_DivExact) &&
        li.b_kind == B_Mult && ri.exp == lri.exp) {
      return SimplifyExp(exp, lli.exp);
    }

    // input:  (exp0 * n0) / n1  where n1 divides n0
    // output: exp0 * (n0 / n1)

    if ((i.b_kind == B_Div || i.b_kind == B_DivExact) &&
        li.b_kind == B_Mult && lri.has_value && ri.has_value &&
        mpz_cmp_si(ri.value, 0) > 0 &&
        mpz_divisible_p(lri.value, ri.value)) {
      Exp *op_exp = MakeBinop(i.b_kind, lri.exp, ri.exp);
      Exp *new_exp = MakeBinop(B_Mult, lli.exp, op_exp);
      return SimplifyExp(exp, new_exp);
    }

    // input:  (exp0 * n0) / n1  where n0 divides n1
    // output: exp0 / (n1 / n0)

    if ((i.b_kind == B_Div || i.b_kind == B_DivExact) &&
        li.b_kind == B_Mult && lri.has_value && ri.has_value &&
        mpz_cmp_si(ri.value, 0) > 0 &&
        mpz_divisible_p(ri.value, lri.value)) {
      Exp *op_exp = MakeBinop(i.b_kind, ri.exp, lri.exp);
      Exp *new_exp = MakeBinop(i.b_kind, lli.exp, op_exp);
      return SimplifyExp(exp, new_exp);
    }

    // input:  (exp0 +/- n0) / n1  where n1 divides n0, exact division only
    // output: (exp0 / n1) +/- (n0 / n1)

    if (i.b_kind == B_DivExact &&
        (li.b_kind == B_Plus || li.b_kind == B_Minus) &&
        lri.has_value && ri.has_value && mpz_cmp_si(ri.value, 0) > 0 &&
        mpz_divisible_p(lri.value, ri.value)) {
      Exp *left_exp = MakeBinop(i.b_kind, lli.exp, ri.exp);
      Exp *right_exp = MakeBinop(i.b_kind, lri.exp, ri.exp);
      Exp *new_exp = MakeBinop(li.b_kind, left_exp, right_exp);
      return SimplifyExp(exp, new_exp);
    }

    // input:  -exp / n
    // output: -(exp / n)

    if ((i.b_kind == B_Div || i.b_kind == B_DivExact) &&
        li.u_kind == U_Neg && ri.has_value) {
      Exp *right_exp = MakeBinop(i.b_kind, lli.exp, ri.exp);
      Exp *new_exp = MakeUnop(U_Neg, right_exp);
      return SimplifyExp(exp, new_exp);
    }
  }

  // fall through simplification cases.

  // input:  exp0 op exp1
  // output: exp1 op exp0
  //   where op is commutative and exp0 > exp1

  // input:  exp0 > exp1
  // output: exp1 < exp0

  // input:  exp0 >= exp1
  // output: exp1 <= exp0

  if (i.b_kind == B_GreaterThan || i.b_kind == B_GreaterEqual ||
      i.b_kind == B_GreaterThanP || i.b_kind == B_GreaterEqualP ||
      (IsCommutativeBinop(i.b_kind) &&
       li.exp->Hash() > ri.exp->Hash())) {

    // don't swap the terms for binops which will be left uninterpreted.
    // the solver will treat 'a & b' and 'b & a' differently; if we change the
    // expression by substituting one of the terms with a value it is known
    // to equal, we don't want to change the order of the two values.
    bool uninterpreted = false;

    switch (i.b_kind) {
    case B_BitwiseAnd:
    case B_BitwiseOr:
    case B_BitwiseXOr:
      uninterpreted = true;
      break;
    case B_Mult:
      if (!li.has_value && !ri.has_value)
        uninterpreted = true;
      break;
    default:
      break;
    }

    if (!uninterpreted) {
      BinopKind new_kind = ReverseBinop(i.b_kind);

      Exp *new_exp =
        MakeBinop(new_kind, ri.exp, li.exp, stride_type, bits, sign);
      return SimplifyExp(exp, new_exp);
    }
  }

  return exp;
}

ExpExit* Exp::MakeExit(Exp *target, Exp *value_kind)
{
  ExpExit xexp(target, value_kind);
  return g_table.Lookup(xexp)->AsExit();
}

ExpInitial* Exp::MakeInitial(Exp *target, Exp *value_kind)
{
  ExpInitial xexp(target, value_kind);
  return g_table.Lookup(xexp)->AsInitial();
}

ExpVal* Exp::MakeVal(Exp *lval, Exp *value_kind, PPoint point, bool relative)
{
  ExpVal xexp(lval, value_kind, point, relative);
  return g_table.Lookup(xexp)->AsVal();
}

ExpFrame* Exp::MakeFrame(Exp *value, FrameId frame_id)
{
  ExpFrame xexp(value, frame_id);
  return g_table.Lookup(xexp)->AsFrame();
}

Exp* ScaleBoundIndex(Type *stride_type, Type *index_type, Exp *index)
{
  size_t stride_width = stride_type->Width();
  size_t index_width = index_type->Width();

  if (stride_width == 0 || index_width == 0)
    return NULL;

  // we can only scale indexes up, i.e. stride_width <= index_width.
  // scaling indexes down via division causes problems when the base of the
  // buffer is not aligned at the stride width.

  if (stride_width == index_width)
    return index;

  if (stride_width < index_width) {
    size_t factor = index_width / stride_width;
    if (stride_width * factor == index_width) {
      Exp *factor_exp = Exp::MakeInt(factor);
      return Exp::MakeBinop(B_Mult, index, factor_exp);
    }
  }

  return NULL;
}

Exp* Exp::MakeNullTest(Exp *target)
{
  switch (target->Kind()) {
    // kinds of expressions which are never NULL.
  case EK_Var:
  case EK_Fld:
  case EK_Rfld:
  case EK_Index:
  case EK_String:
    return MakeInt(0);

    // constant integers are always treated as NULL (this is a loose
    // definition of NULL).
  case EK_Int:
    return MakeInt(1);

  default: break;
  }

  ExpNullTest xexp(target);
  return g_table.Lookup(xexp);
}

Exp* Exp::MakeBound(BoundKind bound_kind, Exp *target, Type *stride_type)
{
  ExpBound xexp(bound_kind, target, stride_type);
  Exp *exp = g_table.Lookup(xexp);

  // handle explicit bounds if type information is available.

  if (target) {
    Exp *new_exp = GetExplicitBound(bound_kind, target, stride_type);
    if (new_exp)
      return SimplifyExp(exp, new_exp, false);
  }

  // input:  Bound(Index(exp0,exp1))
  // output: Bound(exp0) - exp1  (non-offset bounds)
  //     or: Bound(exp0) + exp1  (offset bounds)

  if (target && target->IsIndex()) {
    ExpIndex *ntarget = target->AsIndex();
    Type *element_type = ntarget->GetElementType();
    Exp *inner_target = ntarget->GetTarget();
    Exp *index = ntarget->GetIndex();

    // try to get the new index expression. usually this is the same
    // as the original index, but if the stride and index element
    // types do not match we will try to scale the index.
    Exp *new_index = ScaleBoundIndex(stride_type, element_type, index);

    if (new_index) {
      Exp *new_bound = MakeBound(bound_kind, inner_target, stride_type);

      BinopKind combine_op;
      if (bound_kind == BND_Offset)
        combine_op = B_Plus;
      else
        combine_op = B_Minus;

      Exp *new_exp = MakeBinop(combine_op, new_bound, new_index);
      return SimplifyExp(exp, new_exp, false);
    }
    else if (size_t width = stride_type->Width()) {
      if (width != 1) {
        // punt and rewrite this expression as a byte bound:
        // bound(x, type) == bound(x, byte) / sizeof(type)
        Type *new_stride_type = Type::MakeInt(1, true);
        Exp *outer_exp = MakeBound(bound_kind, target, new_stride_type);
        ExpInt *divide_exp = Exp::MakeInt(width);
        Exp *new_exp = Exp::MakeBinop(B_Div, outer_exp, divide_exp);
        return SimplifyExp(exp, new_exp, false);
      }
      else {
        // we should be able to do the scaling for a byte bound, unless
        // we don't know how wide the index type is. TODO: figure out
        // why we don't always know type widths.
      }
    }
  }

  // input:  Bound((type)exp)
  // output: Bound(exp)

  if (target && target->IsUnop() &&
      target->AsUnop()->GetUnopKind() == U_Coerce) {
    Exp *inner_target = target->AsUnop()->GetOperand();
    Exp *new_exp = exp->ReplaceLvalTarget(inner_target);
    return SimplifyExp(exp, new_exp);
  }

  // input:  Bound(Frame(exp))
  // output: Frame(Bound(exp))

  if (target && target->IsFrame()) {
    ExpFrame *ntarget = target->AsFrame();
    Exp *value = ntarget->GetValue();
    FrameId frame = ntarget->GetFrameId();

    Exp *new_value = exp->ReplaceLvalTarget(value);
    Exp *new_exp = MakeFrame(new_value, frame);
    return SimplifyExp(exp, new_exp);
  }

  // normalize the bound type if necessary.

  if (Type *new_stride_type = NormalizeType(stride_type)) {
    Exp *new_exp = MakeBound(bound_kind, target, new_stride_type);
    return SimplifyExp(exp, new_exp, false);
  }

  return exp;
}

Exp* Exp::MakeDirective(DirectiveKind kind)
{
  ExpDirective xexp(kind);
  return g_table.Lookup(xexp);
}

Exp* Exp::MakeTerminate(Exp *target, Type *stride_type,
                        Exp *terminate_test, ExpInt *terminate_int)
{
  ExpTerminate xexp(target, stride_type, terminate_test, terminate_int);
  ExpTerminate *exp = g_table.Lookup(xexp)->AsTerminate();

  // input:  Terminate(Index(exp0,exp1))
  // output: Terminate(exp0) - exp1

  if (target && target->IsIndex()) {
    ExpIndex *ntarget = target->AsIndex();
    Exp *inner_target = ntarget->GetTarget();
    Exp *index = ntarget->GetIndex();

    bool compatible_type = false;
    Type *element_type = ntarget->GetElementType();

    if (element_type == stride_type) {
      compatible_type = true;
    }
    else if (Type *new_element_type = NormalizeType(element_type)) {
      if (new_element_type == stride_type)
        compatible_type = true;
    }

    if (compatible_type) {
      Exp *new_terminator = exp->ReplaceLvalTarget(inner_target);
      Exp *new_exp = MakeBinop(B_Minus, new_terminator, index);
      return SimplifyExp(exp, new_exp);
    }
  }

  // input:  Terminate((type)exp)
  // output: Terminate(exp)

  if (target && target->IsUnop() &&
      target->AsUnop()->GetUnopKind() == U_Coerce) {
    Exp *inner_target = target->AsUnop()->GetOperand();
    Exp *new_exp = exp->ReplaceLvalTarget(inner_target);
    return SimplifyExp(exp, new_exp);
  }

  // handle null terminator bounds on constant strings.

  if (target && target->IsString() && exp->AsTerminate()->IsNullTerminate()) {
    TypeArray *array_type = target->GetType()->AsArray();
    Type *elem_type = array_type->GetElementType();

    if (elem_type->Width() == 1 && stride_type->Width() == 1) {
      Assert(array_type->GetElementCount() != 0);
      size_t length = array_type->GetElementCount() - 1;

      Exp *new_exp = Exp::MakeInt(length);
      return SimplifyExp(exp, new_exp, false);
    }
  }

  // normalize the stride type if necessary.

  if (Type *new_stride_type = NormalizeType(stride_type)) {
    Exp *new_exp = MakeTerminate(target, new_stride_type,
                                 terminate_test, terminate_int);
    return SimplifyExp(exp, new_exp, false);
  }

  return exp;
}

Exp* Exp::MakeGCSafe(Exp *target, bool needs_root)
{
  ExpGCSafe xexp(target, needs_root);
  return g_table.Lookup(xexp);
}

/////////////////////////////////////////////////////////////////////
// Bit construction
/////////////////////////////////////////////////////////////////////

static inline Bit* SimplifyBit(Exp *exp, Bit *new_bit)
{
  if (g_callback_CvtSimplify)
    g_callback_CvtSimplify(exp, new_bit);

  return new_bit;
}

Bit* Exp::MakeNonZeroBit(Exp *exp)
{
  if (ExpInt *nexp = exp->IfInt()) {
    // input:  BIT(n)
    // output: (n != 0) ? true : false

    mpz_t value;
    mpz_init(value);

    nexp->GetMpzValue(value);
    Bit *new_bit = Bit::MakeConstant(mpz_cmp_si(value, 0) != 0);
    mpz_clear(value);

    return SimplifyBit(exp, new_bit);
  }

  if (ExpUnop *nexp = exp->IfUnop()) {
    UnopKind kind = nexp->GetUnopKind();
    Exp *op_exp = nexp->GetOperand();

    // input:  BIT(ExpUnop(!exp))
    // output: !BIT(exp)

    if (kind == U_LogicalNot) {
      Bit *base_bit = MakeNonZeroBit(op_exp);
      Bit *new_bit = Bit::MakeNot(base_bit);
      return SimplifyBit(exp, new_bit);
    }
  }

  if (ExpBinop *nexp = exp->IfBinop()) {
    BinopKind kind = nexp->GetBinopKind();
    Exp *left = nexp->GetLeftOperand();
    Exp *right = nexp->GetRightOperand();

    long const_val = 0;
    Exp *nonconst = nexp->HasConstant(&const_val);

    // input:  BIT(exp0 && exp1)
    // output: BIT(exp0) && BIT(exp1)

    if (kind == B_LogicalAnd) {
      Bit *left_bit = MakeNonZeroBit(left);
      Bit *right_bit = MakeNonZeroBit(right);
      Bit *new_bit = Bit::MakeAnd(left_bit, right_bit);
      return SimplifyBit(exp, new_bit);
    }

    // input:  BIT(exp0 || exp1)
    // output: BIT(exp0) || BIT(exp1)

    if (kind == B_LogicalOr) {
      Bit *left_bit = MakeNonZeroBit(left);
      Bit *right_bit = MakeNonZeroBit(right);
      Bit *new_bit = Bit::MakeOr(left_bit, right_bit);
      return SimplifyBit(exp, new_bit);
    }

    // input:  BIT(exp != 0)
    //    or:  BIT(0 != exp)
    // output: BIT(exp)

    if (kind == B_NotEqual && nonconst && const_val == 0) {
      Bit *new_bit = MakeNonZeroBit(nonconst);
      return SimplifyBit(exp, new_bit);
    }

    // input:  BIT(exp == 0)
    //    or:  BIT(0 == exp)
    // output: !BIT(exp)

    if (kind == B_Equal && nonconst && const_val == 0) {
      Bit *base_bit = MakeNonZeroBit(nonconst);
      Bit *new_bit = Bit::MakeNot(base_bit);
      return SimplifyBit(exp, new_bit);
    }
  }

  // fallthrough: just make a boolean variable for the expression.
  return Bit::MakeVar(exp);
}

Bit* Exp::MakeCompareBit(BinopKind binop_kind,
                         Exp *left_op, Exp *right_op, Type *stride_type)
{
  Exp *exp = MakeBinop(binop_kind, left_op, right_op, stride_type);
  return MakeNonZeroBit(exp);
}

/////////////////////////////////////////////////////////////////////
// Exp static
/////////////////////////////////////////////////////////////////////

void Exp::GetSubExprs(Exp *exp,
                      Vector<Exp*> *subexprs,
                      Vector<Exp*> *remainders)
{
  Assert(subexprs == NULL || subexprs->Empty());
  Assert(remainders == NULL || remainders->Empty());

  switch (exp->Kind()) {
  case EK_Empty:
  case EK_Var:
    break;
  case EK_Drf: {
    ExpDrf *nexp = exp->AsDrf();
    GetSubExprs(nexp->GetTarget(), subexprs, remainders);
    if (remainders) {
      for (size_t rind = 0; rind < remainders->Size(); rind++)
        remainders->At(rind) = MakeDrf(remainders->At(rind));
    }
    break;
  }
  case EK_Fld: {
    ExpFld *nexp = exp->AsFld();
    GetSubExprs(nexp->GetTarget(), subexprs, remainders);
    if (remainders) {
      Field *field = nexp->GetField();
      for (size_t rind = 0; rind < remainders->Size(); rind++)
        remainders->At(rind) = MakeFld(remainders->At(rind), field);
    }
    break;
  }
  case EK_Rfld: {
    ExpRfld *nexp = exp->AsRfld();
    GetSubExprs(nexp->GetTarget(), subexprs, remainders);
    if (remainders) {
      Field *field = nexp->GetField();
      for (size_t rind = 0; rind < remainders->Size(); rind++)
        remainders->At(rind) = MakeRfld(remainders->At(rind), field);
    }
    break;
  }
  case EK_Index: {
    ExpIndex *nexp = exp->AsIndex();
    GetSubExprs(nexp->GetTarget(), subexprs, remainders);
    if (remainders) {
      Type *elem_type = nexp->GetElementType();
      Exp *index = nexp->GetIndex();
      for (size_t rind = 0; rind < remainders->Size(); rind++) {
        remainders->At(rind) =
          MakeIndex(remainders->At(rind), elem_type, index);
      }
    }
    break;
  }
  default:
    break;
  }

  if (subexprs)
    subexprs->PushBack((Exp*)exp);
  if (remainders) {
    Exp *empty = MakeEmpty();
    remainders->PushBack(empty);
  }
}

Exp* Exp::GetSubExprRemainder(Exp *value, Exp *subexpr)
{
  Vector<Exp*> subexprs;
  Vector<Exp*> remainders;
  GetSubExprs(value, &subexprs, &remainders);

  Exp *res = NULL;
  for (size_t ind = 0; ind < subexprs.Size(); ind++) {
    if (subexpr == subexprs[ind]) {
      res = remainders[ind];
      break;
    }
  }
  Assert(res);
  return res;
}

Exp* Exp::Compose(Exp *exp, Exp *offset)
{
  switch (offset->Kind()) {

  case EK_Empty:
    return exp;

  case EK_Drf: {
    ExpDrf *noffset = offset->AsDrf();
    Exp *ntarget = Compose(exp, noffset->GetTarget());
    return MakeDrf(ntarget);
  }

  case EK_Fld: {
    ExpFld *noffset = offset->AsFld();
    Exp *ntarget = Compose(exp, noffset->GetTarget());

    Field *field = noffset->GetField();
    return MakeFld(ntarget, field);
  }

  case EK_Rfld: {
    ExpRfld *noffset = offset->AsRfld();
    Exp *ntarget = Compose(exp, noffset->GetTarget());

    Field *field = noffset->GetField();
    return MakeRfld(ntarget, field);
  }

  case EK_Index: {
    ExpIndex *noffset = offset->AsIndex();
    Exp *ntarget = Compose(exp, noffset->GetTarget());

    Type *element_type = noffset->GetElementType();
    Exp *index = noffset->GetIndex();
    return MakeIndex(ntarget, element_type, index);
  }

  default:
    Assert(false);
    return NULL;
  }
}

Exp* Exp::GetExplicitBound(BoundKind bound_kind, Exp *target,
                           Type *stride_type)
{
  Type *target_type = target->GetType();

  if (!target->IsVar() && !target->IsFld() &&
      !target->IsIndex() && !target->IsString())
    return NULL;

  if (stride_type->Width() == 0)
    return NULL;

  if (target_type == NULL)
    return NULL;

  // if the expression is an index then make sure this is a multidimensional
  // array, not mismatched indexes into an outer buffer.
  if (target->IsIndex() && !target_type->IsArray())
    return NULL;

  // for expressions indicating variable length fields of a parent structure
  // (0- or 1-length arrays at the end of the structure's list of members),
  // compute a symbolic bound in terms of the bound of the parent structure.
  if (ExpFld *ntarget = target->IfFld()) {
    Exp *inner_target = ntarget->GetTarget();
    Field *field = ntarget->GetField();

    if (TypeArray *ntype = target_type->IfArray()) {
      if (ntype->GetElementCount() <= 1) {
        String *csu_name = field->GetCSUType()->GetCSUName();

        CompositeCSU *csu = CompositeCSUCache.Lookup(csu_name);
        Assert(csu->GetFieldCount() != 0);

        // assuming the last field in the type is the last one listed.
        if (field == csu->GetField(csu->GetFieldCount() - 1).field) {
          // compute the width of the CSU minus the variable length
          // field itself (which is zero bytes for a zero element array).
          size_t base_width = csu->GetWidth() - target_type->Width();
          size_t base_count = base_width / stride_type->Width();

          Exp *csu_bound = MakeBound(bound_kind, inner_target, stride_type);
          Exp *count = MakeInt(base_count);

          CompositeCSUCache.Release(csu_name);

          BinopKind binop = (bound_kind == BND_Offset) ? B_Plus : B_Minus;
          return MakeBinop(binop, csu_bound, count);
        }

        CompositeCSUCache.Release(csu_name);
      }
    }
  }

  if (bound_kind == BND_Upper) {
    // get the width in bytes of the expression's type.
    size_t width = target_type->Width();

    // scale down by the width of the bound's stride type.
    size_t count = width / stride_type->Width();

    return MakeInt(count);
  }

  return NULL;
}

/////////////////////////////////////////////////////////////////////
// Exp
/////////////////////////////////////////////////////////////////////

void Exp::PrintUIRval(OutStream &out, bool parens) const
{
  if (const ExpDrf *nexp = this->IfDrf()) {
    nexp->GetTarget()->PrintUI(out, parens);
  }
  else {
    // only print the '&' for actual program lvalues.
    // these are only a subset of what we consider lvalue expressions.
    switch (m_kind) {
    case EK_Var:
    case EK_Fld:
    case EK_Rfld:
    case EK_Index:
      break;
    default:
      PrintUI(out, parens);
      return;
    }

    out << "&";
    PrintUI(out, true);
  }
}

void Exp::DoVisit(ExpVisitor *visitor)
{
  if (visitor->IsVisiting())
    visitor->Visit(this);
}

Exp* Exp::DoMap(ExpMapper *mapper)
{
  return BaseMap(this, mapper);
}

void Exp::DoMultiMap(ExpMultiMapper *mapper, Vector<Exp*> *res)
{
  return BaseMultiMap(mapper, res);
}

// visitor for checking a variety of subexpression properties of an exp.
class ExpVisitor_AnySub : public ExpVisitor
{
 public:
  Variable *root;
  ExpClobber *clobber_root;
  bool relative;
  bool index;
  Field *base_field;
  size_t num_drf;
  size_t num_fld;
  size_t num_rfld;

  ExpVisitor_AnySub()
    : ExpVisitor(VISK_SubExprs),
      root(NULL), clobber_root(NULL), relative(false), index(false),
      base_field(NULL), num_drf(0), num_fld(0), num_rfld(0)
  {}

  void Visit(Exp *exp)
  {
    if (ExpVar *nexp = exp->IfVar())
      root = nexp->GetVariable();

    if (ExpClobber *nexp = exp->IfClobber())
      clobber_root = nexp;

    if (exp->IsEmpty())
      relative = true;

    if (exp->IsIndex())
      index = true;

    if (ExpFld *nexp = exp->IfFld()) {
      num_fld++;
      if (nexp->GetTarget()->IsEmpty())
        base_field = nexp->GetField();
    }

    if (exp->IsRfld())
      num_rfld++;

    if (exp->IsDrf())
      num_drf++;
  }
};

Variable* Exp::Root()
{
  ExpVisitor_AnySub visitor;
  DoVisit(&visitor);

  return visitor.root;
}

ExpClobber* Exp::ClobberRoot()
{
  ExpVisitor_AnySub visitor;
  DoVisit(&visitor);

  // the clobber root only works for fld/drf offsets from a clobber,
  // not indexes, as if the index contains caller terms we won't be
  // able to construct the corresponding callee value for this expression.
  // TODO: this is a hack.
  return visitor.index ? NULL : visitor.clobber_root;
}

bool Exp::IsRelative()
{
  ExpVisitor_AnySub visitor;
  DoVisit(&visitor);

  return visitor.relative;
}

Field* Exp::BaseField()
{
  ExpVisitor_AnySub visitor;
  DoVisit(&visitor);

  return visitor.base_field;
}

size_t Exp::DrfCount()
{
  ExpVisitor_AnySub visitor;
  DoVisit(&visitor);

  return visitor.num_drf;
}

size_t Exp::FldCount()
{
  ExpVisitor_AnySub visitor;
  DoVisit(&visitor);

  return visitor.num_fld;
}

size_t Exp::RfldCount()
{
  ExpVisitor_AnySub visitor;
  DoVisit(&visitor);

  return visitor.num_rfld;
}

class ExpVisitor_TermCount : public ExpVisitor
{
public:
  size_t term_count;

  ExpVisitor_TermCount()
    : ExpVisitor(VISK_All), term_count(0)
  {}

  void Visit(Exp *exp)
  {
    if (!exp->IsRvalue() && !FoundTerm())
      term_count++;
  }
};
 
size_t Exp::TermCount()
{
  ExpVisitor_TermCount visitor;
  DoVisit(&visitor);

  return visitor.term_count;
}

class ExpVisitor_TermCountExceeds : public ExpVisitor
{
 public:
  size_t max_count;
  size_t cur_count;

  // extra cutoff for *all* visited expressions, to watch for expressions
  // with many rvalues/constants but few lvalues.
  size_t all_count;

  ExpVisitor_TermCountExceeds(size_t _max_count)
    : ExpVisitor(VISK_All), max_count(_max_count), cur_count(0), all_count(0)
  {}

  void Visit(Exp *exp)
  {
    all_count++;
    if (all_count > max_count + 100)
      m_finished = true;

    if (!exp->IsRvalue() && !FoundTerm()) {
      cur_count++;
      if (cur_count > max_count)
        m_finished = true;
    }
  }
};

bool Exp::TermCountExceeds(size_t count)
{
  ExpVisitor_TermCountExceeds visitor(count);
  DoVisit(&visitor);

  return visitor.IsFinished();
}

/////////////////////////////////////////////////////////////////////
// ExpEmpty
/////////////////////////////////////////////////////////////////////

ExpEmpty::ExpEmpty()
  : Exp(EK_Empty)
{}

void ExpEmpty::Print(OutStream &out) const
{}

/////////////////////////////////////////////////////////////////////
// ExpVar
/////////////////////////////////////////////////////////////////////

ExpVar::ExpVar(Variable *var)
  : Exp(EK_Var), m_var(var)
{
  Assert(m_var);
  m_hash = Hash32(m_hash, m_var->Hash());
}

Type* ExpVar::GetType() const
{
  return m_var->GetType();
}

void ExpVar::Print(OutStream &out) const
{
  out << m_var;
}

void ExpVar::MarkChildren() const
{
  m_var->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpDrf
/////////////////////////////////////////////////////////////////////

ExpDrf::ExpDrf(Exp *target)
  : Exp(EK_Drf), m_target(target)
{
  Assert(m_target);
  m_hash = Hash32(m_hash, m_target->Hash());
}

Type* ExpDrf::GetType() const
{
  Type *target_type = m_target->GetType();
  if (target_type && target_type->IsPointer())
    return target_type->AsPointer()->GetTargetType();
  return NULL;
}

Exp* ExpDrf::GetLvalTarget() const
{
  return m_target;
}

Exp* ExpDrf::ReplaceLvalTarget(Exp *new_target)
{
  return MakeDrf(new_target);
}

void ExpDrf::DoVisit(ExpVisitor *visitor)
{
  Exp::DoVisit(visitor);

  if (visitor->IsFinished())
    return;

  if (visitor->Kind() == VISK_Lval) {
    // visit the expression whose value is being accessed.
    visitor->Visit(m_target);
  }

  if (visitor->LvalRecurse()) {
    bool old_found_lval = visitor->SetFoundLval(true);
    bool old_found_term = visitor->SetFoundTerm(true);
    m_target->DoVisit(visitor);
    visitor->SetFoundLval(old_found_lval);
    visitor->SetFoundTerm(old_found_term);
  }
}

Exp* ExpDrf::DoMap(ExpMapper *mapper)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMap(mapper);

  Exp *new_this = NULL;
  Exp *new_target = m_target->DoMap(mapper);
  if (new_target)
    new_this = MakeDrf(new_target);
  return BaseMap(new_this, mapper);
}

void ExpDrf::DoMultiMap(ExpMultiMapper *mapper, Vector<Exp*> *res)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMultiMap(mapper, res);

  BaseMultiMap(mapper, res);

  Vector<Exp*> target_res;
  m_target->DoMultiMap(mapper, &target_res);

  for (size_t ind = 0; ind < target_res.Size(); ind++) {
    Exp *new_this = MakeDrf(target_res[ind]);
    ExpAddResult(new_this, res);

    if (LimitRevertResult(mapper, res, this))
      break;
  }
}

void ExpDrf::Print(OutStream &out) const
{
  out << m_target << "*";
}

void ExpDrf::PrintUI(OutStream &out, bool parens) const
{
  out << "*";
  m_target->PrintUI(out, true);
}

void ExpDrf::MarkChildren() const
{
  m_target->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpFld
/////////////////////////////////////////////////////////////////////

ExpFld::ExpFld(Exp *target, Field *field)
  : Exp(EK_Fld), m_target(target), m_field(field)
{
  Assert(m_target);
  Assert(m_field);
  m_hash = Hash32(m_hash, m_target->Hash());
  m_hash = Hash32(m_hash, m_field->Hash());
}

Type* ExpFld::GetType() const
{
  return m_field->GetType();
}

Exp* ExpFld::GetLvalTarget() const
{
  return m_target;
}

Exp* ExpFld::ReplaceLvalTarget(Exp *new_target)
{
  return MakeFld(new_target, m_field);
}

void ExpFld::DoVisit(ExpVisitor *visitor)
{
  Exp::DoVisit(visitor);

  if (visitor->IsFinished())
    return;

  if (visitor->LvalRecurse()) {
    bool old_found_term = visitor->SetFoundTerm(true);
    m_target->DoVisit(visitor);
    visitor->SetFoundTerm(old_found_term);
  }
}

Exp* ExpFld::DoMap(ExpMapper *mapper)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMap(mapper);

  Exp *new_this = NULL;
  Exp *new_target = m_target->DoMap(mapper);
  if (new_target)
    new_this = MakeFld(new_target, m_field);
  return BaseMap(new_this, mapper);
}

void ExpFld::DoMultiMap(ExpMultiMapper *mapper, Vector<Exp*> *res)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMultiMap(mapper, res);

  BaseMultiMap(mapper, res);

  Vector<Exp*> target_res;
  m_target->DoMultiMap(mapper, &target_res);

  for (size_t ind = 0; ind < target_res.Size(); ind++) {
    Exp *new_this = MakeFld(target_res[ind], m_field);
    ExpAddResult(new_this, res);

    if (LimitRevertResult(mapper, res, this))
      break;
  }
}

void ExpFld::Print(OutStream &out) const
{
  out << m_target << "." << m_field;
}

void ExpFld::PrintUI(OutStream &out, bool parens) const
{
  if (ExpDrf *ntarget = m_target->IfDrf()) {
    ntarget->GetTarget()->PrintUI(out, true);
    out << "->" << m_field;
  }
  else {
    m_target->PrintUI(out, true);
    out << "." << m_field;
  }
}

void ExpFld::MarkChildren() const
{
  m_target->Mark();
  m_field->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpRfld
/////////////////////////////////////////////////////////////////////

ExpRfld::ExpRfld(Exp *target, Field *field)
  : Exp(EK_Rfld), m_target(target), m_field(field)
{
  Assert(m_target);
  Assert(m_field);

  m_hash = Hash32(m_hash, m_target->Hash());
  m_hash = Hash32(m_hash, m_field->Hash());
}

Type* ExpRfld::GetType() const
{
  return m_field->GetCSUType();
}

Exp* ExpRfld::GetLvalTarget() const
{
  return m_target;
}

Exp* ExpRfld::ReplaceLvalTarget(Exp *new_target)
{
  return MakeRfld(new_target, m_field);
}

void ExpRfld::DoVisit(ExpVisitor *visitor)
{
  Exp::DoVisit(visitor);

  if (visitor->IsFinished())
    return;

  if (visitor->LvalRecurse()) {
    bool old_found_term = visitor->SetFoundTerm(true);
    m_target->DoVisit(visitor);
    visitor->SetFoundTerm(old_found_term);
  }
}

Exp* ExpRfld::DoMap(ExpMapper *mapper)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMap(mapper);

  Exp *new_this = NULL;
  Exp *new_target = m_target->DoMap(mapper);
  if (new_target)
    new_this = MakeRfld(new_target, m_field);

  return BaseMap(new_this, mapper);
}

void ExpRfld::DoMultiMap(ExpMultiMapper *mapper, Vector<Exp*> *res)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMultiMap(mapper, res);

  BaseMultiMap(mapper, res);

  Vector<Exp*> target_res;
  m_target->DoMultiMap(mapper, &target_res);

  for (size_t ind = 0; ind < target_res.Size(); ind++) {
    Exp *new_this = MakeRfld(target_res[ind], m_field);
    ExpAddResult(new_this, res);

    if (LimitRevertResult(mapper, res, this))
      break;
  }
}

void ExpRfld::Print(OutStream &out) const
{
  out << m_target << "^" << m_field;
}

void ExpRfld::PrintUI(OutStream &out, bool parens) const
{
  m_target->PrintUI(out, true);
  out << "^" << m_field;
}

void ExpRfld::MarkChildren() const
{
  m_target->Mark();
  m_field->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpIndex
/////////////////////////////////////////////////////////////////////

ExpIndex::ExpIndex(Exp *target, Type *element_type, Exp *index)
  : Exp(EK_Index), m_target(target),
    m_element_type(element_type), m_index(index)
{
  Assert(m_target);
  Assert(m_element_type);
  Assert(m_index);

  // TODO: this assert can trip in cases like 'int[] *x; x[0][0] = 0;'
  // we need to handle this case correctly.
  // Assert(m_element_type->Width() != 0);

  m_hash = Hash32(m_hash, m_target->Hash());
  m_hash = Hash32(m_hash, m_element_type->Hash());
  m_hash = Hash32(m_hash, m_index->Hash());
}

Type* ExpIndex::GetType() const
{
  return m_element_type;
}

Exp* ExpIndex::GetLvalTarget() const
{
  return m_target;
}

Exp* ExpIndex::ReplaceLvalTarget(Exp *new_target)
{
  return MakeIndex(new_target, m_element_type, m_index);
}

bool ExpIndex::IsCompatibleStrideType(Type *type) const
{
  return IsCompatibleNormalizedType(type, m_element_type);
}

void ExpIndex::DoVisit(ExpVisitor *visitor)
{
  Exp::DoVisit(visitor);

  if (visitor->IsFinished())
    return;

  if (visitor->LvalRecurse()) {
    bool old_found_term = visitor->SetFoundTerm(true);
    m_target->DoVisit(visitor);
    visitor->SetFoundTerm(old_found_term);
  }

  if (visitor->LvalRecurse() && visitor->RvalRecurse()) {
    bool old_found_lval = visitor->SetFoundLval(false);
    m_index->DoVisit(visitor);
    visitor->SetFoundLval(old_found_lval);
  }
}

Exp* ExpIndex::DoMap(ExpMapper *mapper)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMap(mapper);

  Exp *new_target = m_target->DoMap(mapper);

  Exp *new_index;
  if (mapper->RvalRecurse())
    new_index = m_index->DoMap(mapper);
  else
    new_index = m_index;

  Exp *new_this = NULL;
  if (new_target && new_index)
    new_this = MakeIndex(new_target, m_element_type, new_index);

  return BaseMap(new_this, mapper);
}

void ExpIndex::DoMultiMap(ExpMultiMapper *mapper, Vector<Exp*> *res)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMultiMap(mapper, res);

  BaseMultiMap(mapper, res);

  Vector<Exp*> target_res;
  m_target->DoMultiMap(mapper, &target_res);

  Vector<Exp*> index_res;
  if (mapper->LvalRecurse() && mapper->RvalRecurse()) {
    m_index->DoMultiMap(mapper, &index_res);
  }
  else {
    index_res.PushBack(m_index);
  }

  for (size_t ind = 0; ind < target_res.Size(); ind++) {
    Exp *new_target = target_res[ind];

    for (size_t xind = 0; xind < index_res.Size(); xind++) {
      Exp *new_this = MakeIndex(new_target, m_element_type,
                                index_res[xind]);
      ExpAddResult(new_this, res);

      if (LimitRevertResult(mapper, res, this))
        return;
    }
  }
}

void ExpIndex::Print(OutStream &out) const
{
  out << m_target << "[" << m_index << "]" << "{" << m_element_type << "}";
}

void ExpIndex::PrintUI(OutStream &out, bool parens) const
{
  // the Drf is implicit when used with an index.
  if (ExpDrf *ntarget = m_target->IfDrf())
    ntarget->GetTarget()->PrintUI(out, true);
  else
    m_target->PrintUI(out, true);

  out << "[";
  m_index->PrintUIRval(out, false);
  out << "]";
}

void ExpIndex::MarkChildren() const
{
  m_target->Mark();
  m_element_type->Mark();
  m_index->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpString
/////////////////////////////////////////////////////////////////////

ExpString::ExpString(TypeArray *type, DataString *str)
  : Exp(EK_String), m_type(type), m_str(str)
{
  Assert(m_type);
  Assert(m_str);

  // element types must be an integer of some kind.
  Assert(m_type->GetElementType()->IsInt());

  m_hash = Hash32(m_hash, m_type->Hash());
  m_hash = Hash32(m_hash, m_str->Hash());
}

const char* ExpString::GetStringCStr() const
{
  if (m_type->AsArray()->GetElementType()->Width() == 1) {
    size_t length = m_str->ValueLength();
    const uint8_t *val = m_str->Value();

    if (length > 0 && val[length-1] == 0)
      return (const char*) val;
  }

  return NULL;
}

Type* ExpString::GetType() const
{
  return m_type;
}

void ExpString::Print(OutStream &out) const
{
  // try a nicer formatting for NULL terminated character strings
  // (the typical case). don't use GetStringCStr so we treat strings
  // with intermediate NULLs correctly.

  if (m_type->AsArray()->GetElementType()->Width() == 1) {
    size_t length = m_str->ValueLength();
    const uint8_t *val = m_str->Value();

    if (length > 0 && val[length-1] == 0) {
      out << "\"";
      PrintString(out, val, length-1);
      out << "\"";
      return;
    }
  }

  // fall through.
  out << m_str;
}

void ExpString::MarkChildren() const
{
  m_type->Mark();
  m_str->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpClobber
/////////////////////////////////////////////////////////////////////

static inline Type* GetValueType(Exp *lval, Exp *value_kind)
{
  if (value_kind) {
    // terminator positions do not have types.
    return NULL;
  }
  else {
    Type *lval_type = lval->GetType();
    if (lval_type && lval_type->IsPointer())
      return lval_type->AsPointer()->GetTargetType();
    return NULL;
  }
}

ExpClobber::ExpClobber(Exp *callee, Exp *value_kind, Exp *overwrite,
                       PPoint point, Location *location)
  : Exp(EK_Clobber), m_callee(callee),
    m_value_kind(value_kind), m_overwrite(overwrite),
    m_point(point), m_location(location)
{
  Assert(m_callee);
  Assert(m_overwrite);
  Assert(m_point);

  m_hash = Hash32(m_hash, m_callee->Hash());
  m_hash = Hash32(m_hash, m_overwrite->Hash());
  if (m_value_kind)
    m_hash = Hash32(m_hash, m_value_kind->Hash());
  m_hash = Hash32(m_hash, m_point);
  if (m_location)
    m_hash = Hash32(m_hash, m_location->Hash());
}

Type* ExpClobber::GetType() const
{
  return GetValueType(m_overwrite, m_value_kind);
}

Exp* ExpClobber::GetLvalTarget() const
{
  return m_overwrite;
}

void ExpClobber::Print(OutStream &out) const
{
  out << "cval(" << m_callee;

  if (m_value_kind)
    out << ",v" << m_value_kind;

  out << ",p" << m_point;

  if (m_location)
    out << "," << m_location->Line();

  out << ")";
}

void ExpClobber::MarkChildren() const
{
  m_callee->Mark();
  m_overwrite->Mark();
  if (m_value_kind)
    m_value_kind->Mark();
  if (m_location)
    m_location->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpInt
/////////////////////////////////////////////////////////////////////

ExpInt::ExpInt(const char *value)
  : Exp(EK_Int), m_value(value)
{
  Assert(m_value);

  // the string should be in base 10.
  const char *tmp = m_value;
  if (*tmp == '-')
    tmp++;
  do {
    Assert(*tmp >= '0' && *tmp <= '9');
  } while (*++tmp);

  m_hash = HashBlock(m_hash, (const uint8_t*) m_value, strlen(m_value));
}

void ExpInt::Print(OutStream &out) const
{
  out << m_value;
}

void ExpInt::Persist()
{
  char *new_value = new char[strlen(m_value) + 1];
  strcpy(new_value, m_value);

  m_value = new_value;
  mpz_init_set_str(m_mpz, m_value, 10);
}

void ExpInt::UnPersist()
{
  delete[] m_value;
  mpz_clear(m_mpz);
}

/////////////////////////////////////////////////////////////////////
// ExpFloat
/////////////////////////////////////////////////////////////////////

ExpFloat::ExpFloat(const char *value)
  : Exp(EK_Float), m_value(value)
{
  Assert(m_value);
  m_hash = HashBlock(m_hash, (const uint8_t*) m_value, strlen(m_value));
}

void ExpFloat::Print(OutStream &out) const
{
  out << m_value;
}

void ExpFloat::Persist()
{
  char *new_value = new char[strlen(m_value) + 1];
  strcpy(new_value, m_value);
  m_value = new_value;
}

void ExpFloat::UnPersist()
{
  delete[] m_value;
}

/////////////////////////////////////////////////////////////////////
// ExpUnop
/////////////////////////////////////////////////////////////////////

ExpUnop::ExpUnop(UnopKind unop_kind, Exp *op,
                 size_t bits, bool sign)
  : Exp(EK_Unop, bits, sign), m_unop_kind(unop_kind), m_op(op)
{
  Assert(m_unop_kind != U_Invalid);
  Assert(m_op);

  if (bits == 0)
    Assert(sign);

  m_hash = Hash32(m_hash, m_unop_kind);
  m_hash = Hash32(m_hash, m_op->Hash());
}

void ExpUnop::DoVisit(ExpVisitor *visitor)
{
  Exp::DoVisit(visitor);

  if (visitor->IsFinished())
    return;

  if (visitor->RvalRecurse())
    m_op->DoVisit(visitor);
}

Exp* ExpUnop::DoMap(ExpMapper *mapper)
{
  if (!mapper->RvalRecurse())
    return Exp::DoMap(mapper);

  Exp *new_this = NULL;
  Exp *new_op = m_op->DoMap(mapper);
  if (new_op)
    new_this = MakeUnop(m_unop_kind, new_op, m_bits, m_sign);
  return BaseMap(new_this, mapper);
}

void ExpUnop::DoMultiMap(ExpMultiMapper *mapper, Vector<Exp*> *res)
{
  if (!mapper->RvalRecurse())
    return Exp::DoMultiMap(mapper, res);

  BaseMultiMap(mapper, res);

  Vector<Exp*> op_res;
  m_op->DoMultiMap(mapper, &op_res);

  for (size_t ind = 0; ind < op_res.Size(); ind++) {
    Exp *new_this = MakeUnop(m_unop_kind, op_res[ind], m_bits, m_sign);
    ExpAddResult(new_this, res);

    if (LimitRevertResult(mapper, res, this))
      break;
  }
}

void ExpUnop::Print(OutStream &out) const
{
  // special pretty printing for coerce.
  if (m_unop_kind == U_Coerce) {
    Assert(m_bits);
    out << "(" << (m_sign ? "s" : "u") << m_bits << ")";
  }
  else {
    const char *unop = UnopString(m_unop_kind);
    out << unop;

    if (m_bits)
      out << "{" << (m_sign ? "s" : "u") << m_bits << "}";
  }

  out << m_op;
}

void ExpUnop::PrintUI(OutStream &out, bool parens) const
{
  const char *unop = UnopString(m_unop_kind, true);
  out << unop;
  m_op->PrintUIRval(out, true);
}

void ExpUnop::MarkChildren() const
{
  m_op->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpBinop
/////////////////////////////////////////////////////////////////////

ExpBinop::ExpBinop(BinopKind binop_kind,
                   Exp *left_op, Exp *right_op, Type *stride_type,
                   size_t bits, bool sign)
  : Exp(EK_Binop, bits, sign), m_binop_kind(binop_kind),
    m_left_op(left_op), m_right_op(right_op), m_stride_type(stride_type)
{
  Assert(m_binop_kind != B_Invalid);
  Assert(m_left_op);
  Assert(m_right_op);

  Assert((m_stride_type != NULL) == IsPointerBinop(m_binop_kind));

  if (bits == 0)
    Assert(sign);

  // binops on pointers and comparisons can never overflow, and should not
  // have an associated bit width.
  if (stride_type || IsCompareBinop(binop_kind))
    Assert(bits == 0);

  m_hash = Hash32(m_hash, m_binop_kind);
  m_hash = Hash32(m_hash, m_left_op->Hash());
  m_hash = Hash32(m_hash, m_right_op->Hash());
  if (m_stride_type)
    m_hash = Hash32(m_hash, m_stride_type->Hash());
}

bool ExpBinop::IsCompatibleStrideType(Type *type) const
{
  if (m_stride_type)
    return IsCompatibleNormalizedType(type, m_stride_type);
  return false;
}

void ExpBinop::DoVisit(ExpVisitor *visitor)
{
  Exp::DoVisit(visitor);

  if (visitor->IsFinished())
    return;

  if (visitor->RvalRecurse()) {
    m_left_op->DoVisit(visitor);
    m_right_op->DoVisit(visitor);
  }
}

Exp* ExpBinop::DoMap(ExpMapper *mapper)
{
  if (!mapper->RvalRecurse())
    return Exp::DoMap(mapper);

  Exp *new_this = NULL;
  Exp *new_left_op = m_left_op->DoMap(mapper);
  Exp *new_right_op = m_right_op->DoMap(mapper);
  if (new_left_op && new_right_op) {
    new_this = MakeBinop(m_binop_kind, new_left_op, new_right_op,
                         m_stride_type, m_bits, m_sign);
  }
  return BaseMap(new_this, mapper);
}

void ExpBinop::DoMultiMap(ExpMultiMapper *mapper, Vector<Exp*> *res)
{
  if (!mapper->RvalRecurse())
    return Exp::DoMultiMap(mapper, res);

  BaseMultiMap(mapper, res);

  Vector<Exp*> left_op_res;
  Vector<Exp*> right_op_res;
  m_left_op->DoMultiMap(mapper, &left_op_res);
  m_right_op->DoMultiMap(mapper, &right_op_res);

  for (size_t lind = 0; lind < left_op_res.Size(); lind++) {
    Exp *new_left_op = left_op_res[lind];

    for (size_t rind = 0; rind < right_op_res.Size(); rind++) {
      Exp *new_right_op = right_op_res[rind];
      Exp *new_this = MakeBinop(m_binop_kind, new_left_op, new_right_op,
                                m_stride_type, m_bits, m_sign);
      ExpAddResult(new_this, res);

      if (LimitRevertResult(mapper, res, this))
        return;
    }
  }
}

void ExpBinop::Print(OutStream &out) const
{
  const char *binop = BinopString(m_binop_kind);

  out << "(" << m_left_op << " " << binop;

  if (m_bits)
    out << "{" << (m_sign ? "s" : "u") << m_bits << "}";
  if (m_stride_type)
    out << "{" << m_stride_type << "}";

  out << " " << m_right_op << ")";
}

void ExpBinop::PrintUI(OutStream &out, bool parens) const
{
  const char *binop = BinopString(m_binop_kind, true);

  if (parens)
    out << "(";

  m_left_op->PrintUIRval(out, true);
  out << " " << binop << " ";
  m_right_op->PrintUIRval(out, true);

  if (parens)
    out << ")";
}

void ExpBinop::MarkChildren() const
{
  m_left_op->Mark();
  m_right_op->Mark();
  if (m_stride_type != NULL)
    m_stride_type->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpExit
/////////////////////////////////////////////////////////////////////

ExpExit::ExpExit(Exp *target, Exp *value_kind)
  : Exp(EK_Exit), m_target(target), m_value_kind(value_kind)
{
  Assert(m_target);

  m_hash = Hash32(m_hash, m_target->Hash());
  if (m_value_kind)
    m_hash = Hash32(m_hash, m_value_kind->Hash());
}

Type* ExpExit::GetType() const
{
  return GetValueType(m_target, m_value_kind);
}

Exp* ExpExit::GetLvalTarget() const
{
  return m_target;
}

Exp* ExpExit::ReplaceLvalTarget(Exp *new_target)
{
  return MakeExit(new_target, m_value_kind);
}

void ExpExit::Print(OutStream &out) const
{
  out << "pdrf(" << m_target;
  if (m_value_kind)
    out << "," << m_value_kind;
  out << ")";
}

void ExpExit::PrintUI(OutStream &out, bool parens) const
{
  out << "exit(";

  Exp *new_exp = NULL;
  if (m_value_kind)
    new_exp = m_value_kind->ReplaceLvalTarget(m_target);
  else
    new_exp = MakeDrf(m_target);

  new_exp->PrintUIRval(out, false);

  out << ")";
}

void ExpExit::MarkChildren() const
{
  m_target->Mark();
  if (m_value_kind)
    m_value_kind->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpInitial
/////////////////////////////////////////////////////////////////////

ExpInitial::ExpInitial(Exp *target, Exp *value_kind)
  : Exp(EK_Initial), m_target(target), m_value_kind(value_kind)
{
  Assert(m_target);

  m_hash = Hash32(m_hash, m_target->Hash());
  if (m_value_kind)
    m_hash = Hash32(m_hash, m_value_kind->Hash());
}

Type* ExpInitial::GetType() const
{
  return GetValueType(m_target, m_value_kind);
}

Exp* ExpInitial::GetLvalTarget() const
{
  return m_target;
}

Exp* ExpInitial::ReplaceLvalTarget(Exp *new_target)
{
  return MakeInitial(new_target, m_value_kind);
}

void ExpInitial::Print(OutStream &out) const
{
  out << "initial(" << m_target;
  if (m_value_kind)
    out << "," << m_value_kind;
  out << ")";
}

void ExpInitial::PrintUI(OutStream &out, bool parens) const
{
  out << "initial(";

  Exp *new_exp = NULL;
  if (m_value_kind)
    new_exp = m_value_kind->ReplaceLvalTarget(m_target);
  else
    new_exp = MakeDrf(m_target);

  new_exp->PrintUIRval(out, false);

  out << ")";
}

void ExpInitial::MarkChildren() const
{
  m_target->Mark();
  if (m_value_kind)
    m_value_kind->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpVal
/////////////////////////////////////////////////////////////////////

ExpVal::ExpVal(Exp *lval, Exp *value_kind, PPoint point, bool relative)
  : Exp(EK_Val, 0, true),
    m_lval(lval), m_value_kind(value_kind),
    m_point(point), m_relative(relative)
{
  Assert(m_lval);
  Assert(m_point);

  m_hash = Hash32(m_hash, m_lval->Hash());
  if (m_value_kind)
    m_hash = Hash32(m_hash, m_value_kind->Hash());
  m_hash = Hash32(m_hash, m_point);
  m_hash = Hash32(m_hash, m_relative);
}

Type* ExpVal::GetType() const
{
  return GetValueType(m_lval, m_value_kind);
}

void ExpVal::Print(OutStream &out) const
{
  if (m_relative)
    out << "eval(" << m_lval;
  else
    out << "val(" << m_lval;
  if (m_value_kind)
    out << "," << m_value_kind;
  out << "," << m_point << ")";
}

void ExpVal::MarkChildren() const
{
  m_lval->Mark();
  if (m_value_kind)
    m_value_kind->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpFrame
/////////////////////////////////////////////////////////////////////

ExpFrame::ExpFrame(Exp *value, FrameId frame_id)
  : Exp(EK_Frame, value->Bits(), value->Sign()),
    m_value(value), m_frame_id(frame_id)
{
  Assert(m_value);

  m_hash = Hash32(m_hash, m_value->Hash());
  m_hash = Hash32(m_hash, m_frame_id);
}

void ExpFrame::Print(OutStream &out) const
{
  out << "frame(" << m_value << "," << m_frame_id << ")";
}

void ExpFrame::PrintUI(OutStream &out, bool parens) const
{
  Exp *new_value = ExpConvertExitClobber(m_value);

  out << "frame(";
  new_value->PrintUI(out, false);
  out << ")";
}

void ExpFrame::MarkChildren() const
{
  m_value->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpNullTest
/////////////////////////////////////////////////////////////////////

ExpNullTest::ExpNullTest(Exp *target)
  : Exp(EK_NullTest), m_target(target)
{
  m_hash = Hash32(m_hash, m_target->Hash());
}

Exp* ExpNullTest::GetLvalTarget() const
{
  return m_target;
}

Exp* ExpNullTest::ReplaceLvalTarget(Exp *new_target)
{
  return MakeNullTest(new_target);
}

void ExpNullTest::DoVisit(ExpVisitor *visitor)
{
  Assert(m_target);
  Exp::DoVisit(visitor);

  if (visitor->IsFinished())
    return;

  if (visitor->LvalRecurse()) {
    bool old_found_term = visitor->SetFoundTerm(true);
    m_target->DoVisit(visitor);
    visitor->SetFoundTerm(old_found_term);
  }
}

Exp* ExpNullTest::DoMap(ExpMapper *mapper)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMap(mapper);
  Assert(m_target);

  Exp *new_this = NULL;
  Exp *new_target = m_target->DoMap(mapper);
  if (new_target)
    new_this = MakeNullTest(new_target);
  return BaseMap(new_this, mapper);
}

void ExpNullTest::DoMultiMap(ExpMultiMapper *mapper, Vector<Exp*> *res)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMultiMap(mapper, res);
  Assert(m_target);

  BaseMultiMap(mapper, res);

  Vector<Exp*> target_res;
  m_target->DoMultiMap(mapper, &target_res);

  for (size_t ind = 0; ind < target_res.Size(); ind++) {
    Exp *new_this = MakeNullTest(target_res[ind]);
    ExpAddResult(new_this, res);

    if (LimitRevertResult(mapper, res, this))
      break;
  }
}

void ExpNullTest::Print(OutStream &out) const
{
  out << "null(" << m_target << ")";
}

void ExpNullTest::PrintUI(OutStream &out, bool parens) const
{
  out << "null(";
  m_target->PrintUIRval(out, false);
  out << ")";
}

void ExpNullTest::MarkChildren() const
{
  m_target->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpBound
/////////////////////////////////////////////////////////////////////

ExpBound::ExpBound(BoundKind bound_kind, Exp *target, Type *stride_type)
  : Exp(EK_Bound), m_bound_kind(bound_kind),
    m_target(target), m_stride_type(stride_type)
{
  Assert(m_stride_type);

  m_hash = Hash32(m_hash, m_bound_kind);
  if (m_target)
    m_hash = Hash32(m_hash, m_target->Hash());
  m_hash = Hash32(m_hash, m_stride_type->Hash());
}

Exp* ExpBound::GetLvalTarget() const
{
  return m_target;
}

Exp* ExpBound::ReplaceLvalTarget(Exp *new_target)
{
  return MakeBound(m_bound_kind, new_target, m_stride_type);
}

bool ExpBound::IsCompatibleStrideType(Type *type) const
{
  return IsCompatibleNormalizedType(type, m_stride_type);
}

void ExpBound::DoVisit(ExpVisitor *visitor)
{
  Assert(m_target);
  Exp::DoVisit(visitor);

  if (visitor->IsFinished())
    return;

  if (visitor->LvalRecurse()) {
    bool old_found_term = visitor->SetFoundTerm(true);
    m_target->DoVisit(visitor);
    visitor->SetFoundTerm(old_found_term);
  }
}

Exp* ExpBound::DoMap(ExpMapper *mapper)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMap(mapper);
  Assert(m_target);

  Exp *new_this = NULL;
  Exp *new_target = m_target->DoMap(mapper);
  if (new_target)
    new_this = MakeBound(m_bound_kind, new_target, m_stride_type);
  return BaseMap(new_this, mapper);
}

void ExpBound::DoMultiMap(ExpMultiMapper *mapper, Vector<Exp*> *res)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMultiMap(mapper, res);
  Assert(m_target);

  BaseMultiMap(mapper, res);

  Vector<Exp*> target_res;
  m_target->DoMultiMap(mapper, &target_res);

  for (size_t ind = 0; ind < target_res.Size(); ind++) {
    Exp *new_this = MakeBound(m_bound_kind, target_res[ind], m_stride_type);
    ExpAddResult(new_this, res);

    if (LimitRevertResult(mapper, res, this))
      break;
  }
}

void ExpBound::Print(OutStream &out) const
{
  const char *bound = BoundString(m_bound_kind);

  out << bound << "(";
  if (m_target)
    out << m_target << ",";
  out << m_stride_type << ")";
}

void ExpBound::PrintUI(OutStream &out, bool parens) const
{
  Assert(m_target);

  const char *bound = NULL;
  switch (m_bound_kind) {
  case BND_Lower:   bound = "lbound"; break;
  case BND_Upper:   bound = "ubound"; break;
  case BND_Offset:  bound = "offset"; break;
  default:          Assert(false);
  }

  out << bound << "(";
  m_target->PrintUIRval(out, false);
  out << "," << m_stride_type << ")";
}

void ExpBound::MarkChildren() const
{
  if (m_target)
    m_target->Mark();
  m_stride_type->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpTerminate
/////////////////////////////////////////////////////////////////////

ExpDirective::ExpDirective(DirectiveKind kind)
  : Exp(EK_Directive), m_directive_kind(kind)
{
  m_hash = Hash32(m_hash, m_directive_kind);
}

void ExpDirective::Print(OutStream &out) const
{
  out << "directive(" << DirectiveString(m_directive_kind) << ")";
}

/////////////////////////////////////////////////////////////////////
// ExpTerminate
/////////////////////////////////////////////////////////////////////

ExpTerminate::ExpTerminate(Exp *target, Type *stride_type,
                           Exp *terminate_test, ExpInt *terminate_int)
  : Exp(EK_Terminate), m_target(target), m_stride_type(stride_type),
    m_terminate_test(terminate_test), m_terminate_int(terminate_int)
{
  Assert(m_stride_type);
  Assert(m_stride_type->Width());

  Assert(m_terminate_test);
  Assert(m_terminate_int);

  if (m_target)
    m_hash = Hash32(m_hash, m_target->Hash());
  m_hash = Hash32(m_hash, m_stride_type->Hash());
  m_hash = Hash32(m_hash, m_terminate_test->Hash());
  m_hash = Hash32(m_hash, m_terminate_int->Hash());
}

Exp* ExpTerminate::GetLvalTarget() const
{
  return m_target;
}

Exp* ExpTerminate::ReplaceLvalTarget(Exp *new_target)
{
  return MakeTerminate(new_target, m_stride_type,
                       m_terminate_test, m_terminate_int);
}

bool ExpTerminate::IsCompatibleStrideType(Type *type) const
{
  return IsCompatibleNormalizedType(type, m_stride_type);
}

void ExpTerminate::DoVisit(ExpVisitor *visitor)
{
  Assert(m_target);
  Exp::DoVisit(visitor);

  if (visitor->IsFinished())
    return;

  if (visitor->LvalRecurse()) {
    bool old_found_term = visitor->SetFoundTerm(true);
    m_target->DoVisit(visitor);
    visitor->SetFoundTerm(old_found_term);
  }
}

Exp* ExpTerminate::DoMap(ExpMapper *mapper)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMap(mapper);
  Assert(m_target);

  Exp *new_this = NULL;
  Exp *new_target = m_target->DoMap(mapper);
  if (new_target) {
    new_this = MakeTerminate(new_target, m_stride_type,
                             m_terminate_test, m_terminate_int);
  }
  return BaseMap(new_this, mapper);
}

void ExpTerminate::DoMultiMap(ExpMultiMapper *mapper, Vector<Exp*> *res)
{
  if (!mapper->LvalRecurse())
    return Exp::DoMultiMap(mapper, res);
  Assert(m_target);

  BaseMultiMap(mapper, res);

  Vector<Exp*> target_res;
  m_target->DoMultiMap(mapper, &target_res);

  for (size_t ind = 0; ind < target_res.Size(); ind++) {
    Exp *new_this = MakeTerminate(target_res[ind], m_stride_type,
                                  m_terminate_test, m_terminate_int);
    ExpAddResult(new_this, res);

    if (LimitRevertResult(mapper, res, this))
      break;
  }
}

void ExpTerminate::Print(OutStream &out) const
{
  if (IsNullTerminate())
    out << "zterm(";
  else
    out << "term(";

  if (m_target)
    out << m_target << ",";
  out << m_stride_type;

  if (!IsNullTerminate())
    out << "," << m_terminate_test << "," << m_terminate_int;

  out << ")";
}

void ExpTerminate::PrintUI(OutStream &out, bool parens) const
{
  Assert(m_target);

  if (IsNullTerminate())
    out << "zterm(";
  else
    out << "term(";

  m_target->PrintUIRval(out, false);
  out << "," << m_stride_type;

  if (!IsNullTerminate())
    out << "," << m_terminate_test << "," << m_terminate_int;

  out << ")";
}

void ExpTerminate::MarkChildren() const
{
  if (m_target)
    m_target->Mark();
  m_stride_type->Mark();
  m_terminate_test->Mark();
  m_terminate_int->Mark();
}

/////////////////////////////////////////////////////////////////////
// ExpGCSafe
/////////////////////////////////////////////////////////////////////

ExpGCSafe::ExpGCSafe(Exp *target, bool needs_root)
  : Exp(EK_GCSafe), m_target(target), m_needs_root(needs_root)
{
  if (m_target)
    m_hash = Hash32(m_hash, m_target->Hash());
  m_hash = Hash32(m_hash, m_needs_root);
}

Exp* ExpGCSafe::GetLvalTarget() const
{
  return m_target;
}

Exp* ExpGCSafe::ReplaceLvalTarget(Exp *new_target)
{
  return MakeGCSafe(new_target, m_needs_root);
}

void ExpGCSafe::DoVisit(ExpVisitor *visitor)
{
  Exp::DoVisit(visitor);

  if (visitor->IsFinished())
    return;

  if (visitor->LvalRecurse() && m_target) {
    bool old_found_term = visitor->SetFoundTerm(true);
    m_target->DoVisit(visitor);
    visitor->SetFoundTerm(old_found_term);
  }
}

Exp* ExpGCSafe::DoMap(ExpMapper *mapper)
{
  if (!mapper->LvalRecurse() || !m_target)
    return Exp::DoMap(mapper);

  Exp *new_this = NULL;
  Exp *new_target = m_target->DoMap(mapper);
  if (new_target)
    new_this = MakeGCSafe(new_target, m_needs_root);
  return BaseMap(new_this, mapper);
}

void ExpGCSafe::DoMultiMap(ExpMultiMapper *mapper, Vector<Exp*> *res)
{
  if (!mapper->LvalRecurse() || !m_target)
    return Exp::DoMultiMap(mapper, res);

  BaseMultiMap(mapper, res);

  Vector<Exp*> target_res;
  m_target->DoMultiMap(mapper, &target_res);

  for (size_t ind = 0; ind < target_res.Size(); ind++) {
    Exp *new_this = MakeGCSafe(target_res[ind], m_needs_root);
    ExpAddResult(new_this, res);

    if (LimitRevertResult(mapper, res, this))
      break;
  }
}

void ExpGCSafe::Print(OutStream &out) const
{
  const char *name = m_needs_root ? "needsroot" : "gcsafe";
  out << name << "(";
  if (m_target)
    out << m_target;
  out << ")";
}

void ExpGCSafe::PrintUI(OutStream &out, bool parens) const
{
  const char *name = m_needs_root ? "needsroot" : "gcsafe";
  out << name << "(";
  if (m_target)
    m_target->PrintUI(out, false);
  out << ")";
}

void ExpGCSafe::MarkChildren() const
{
  if (m_target)
    m_target->Mark();
}

/////////////////////////////////////////////////////////////////////
// Exp utility
/////////////////////////////////////////////////////////////////////

class ReplaceExpMapper : public ExpMapper
{
 public:
  Exp *old_exp;
  Exp *new_exp;

  ReplaceExpMapper(Exp *_old_exp, Exp *_new_exp)
    : ExpMapper(VISK_All, WIDK_Drop), old_exp(_old_exp), new_exp(_new_exp)
  {}

  Exp* Map(Exp *exp, Exp *old)
  {
    Assert(exp);

    if (old == old_exp)
      return new_exp;
    return exp;
  }
};

Exp* ExpReplaceExp(Exp *exp, Exp *old_exp, Exp *new_exp)
{
  ReplaceExpMapper mapper(old_exp, new_exp);
  return exp->DoMap(&mapper);
}

Bit* BitReplaceExp(Bit *bit, Exp *old_exp, Exp *new_exp)
{
  ReplaceExpMapper mapper(old_exp, new_exp);
  return bit->DoMap(&mapper);
}

// mapper to replace all exit and clobber expressions with
// the corresponding Drf or other expression.
class ConvertExitClobberMapper : public ExpMapper
{
public:
  ConvertExitClobberMapper()
    : ExpMapper(VISK_All, WIDK_Drop)
  {}

  Exp* Map(Exp *value, Exp *old)
  {
    Exp *target = NULL;
    Exp *value_kind = NULL;

    if (ExpExit *nvalue = value->IfExit()) {
      target = nvalue->GetTarget();
      value_kind = nvalue->GetValueKind();
    }

    if (ExpClobber *nvalue = value->IfClobber()) {
      target = nvalue->GetOverwrite();
      value_kind = nvalue->GetValueKind();
    }

    if (!target)
      return value;

    // feed the targeted expression back into the mapper,
    // as this outer exp was treated as a leaf.
    Exp *new_target = target->DoMap(this);

    if (value_kind)
      return value_kind->ReplaceLvalTarget(new_target);
    else
      return Exp::MakeDrf(new_target);
  }
};

Exp* ExpConvertExitClobber(Exp *exp)
{
  ConvertExitClobberMapper mapper;
  return exp->DoMap(&mapper);
}

Bit* BitConvertExitClobber(Bit *bit)
{
  ConvertExitClobberMapper mapper;
  return bit->DoMap(&mapper);
}

NAMESPACE_XGILL_END
