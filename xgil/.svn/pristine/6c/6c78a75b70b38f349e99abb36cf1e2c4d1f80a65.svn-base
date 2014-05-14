
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

#include "nullterm.h"
#include <imlang/trace.h>

NAMESPACE_XGILL_BEGIN

class TerminateVisitor : public ExpVisitor
{
public:
  ExpDrf *m_lval;
  ExpInt *m_int_exp;
  bool m_exclude;

  TerminateVisitor()
    : ExpVisitor(VISK_BitLeaf), m_lval(NULL), m_int_exp(NULL), m_exclude(false)
  {}

  void SetTest(ExpDrf *lval, ExpInt *int_exp)
  {
    if (m_exclude)
      return;

    if (m_lval) {
      if (m_lval != lval) {
        m_exclude = true;
        m_lval = NULL;
        m_int_exp = NULL;
      }
      else if (m_int_exp != int_exp) {
        // if the lvalue is compared against multiple ints then treat
        // as a comparison against zero.
        m_int_exp = Exp::MakeInt(0);
      }
    }
    else {
      m_lval = lval;
      m_int_exp = int_exp;
    }
  }

  void Visit(Exp *test)
  {
    // match against particular test forms: *x, *x == n, *x != n

    if (ExpDrf *ntest = test->IfDrf()) {
      ExpInt *int_exp = Exp::MakeInt(0);
      SetTest(ntest, int_exp);
      return;
    }

    if (ExpBinop *ntest = test->IfBinop()) {
      BinopKind kind = NonPointerBinop(ntest->GetBinopKind());

      if (kind == B_Equal || kind == B_NotEqual) {
        long value;
        if (Exp *nonconst = ntest->HasConstant(&value)) {
          if (ExpDrf *nnonconst = nonconst->IfDrf()) {
            ExpInt *int_exp = Exp::MakeInt(value);
            SetTest(nnonconst, int_exp);
            return;
          }
        }
      }
    }
  }
};

// try to get lval and int_exp such that bit can be interpreted as a test
// of lval for the constant int_exp: if lval == int_exp, either bit or
// its negation definitely won't hold, while if lval != int_exp that same
// condition may or may not hold.
bool GetConstantTest(Bit *bit, ExpDrf **lval, ExpInt **int_exp)
{
  // skip any leading negation.
  if (bit->Kind() == BIT_Not)
    bit = bit->GetOperand(0);

  TerminateVisitor visitor;
  bit->DoVisit(&visitor);

  if (visitor.m_exclude || !visitor.m_lval)
    return false;

  *lval = visitor.m_lval;
  *int_exp = visitor.m_int_exp;

  return true;
}

// find the lvalues (relative to block entry) which might be used in
// a terminator test.
void InferTerminatorTests(BlockSummary *sum,
                          const Vector<Exp*> &arithmetic_list,
                          Vector<TerminatorInfo> *terminators)
{
  BlockMemory *mcfg = sum->GetMemory();
  BlockCFG *cfg = mcfg->GetCFG();

  for (size_t ind = 0; ind < cfg->GetEdgeCount(); ind++) {
    if (PEdgeAssume *edge = cfg->GetEdge(ind)->IfAssume()) {
      Bit *edge_cond = mcfg->GetEdgeCond(edge);

      if (!edge_cond)
        continue;

      ExpDrf *compare_lval = NULL;
      ExpInt *terminate_int = NULL;

      if (!GetConstantTest(edge_cond, &compare_lval, &terminate_int))
        continue;

      // the patterns we are matching against on the target are
      // *x, x[i], x->f, and x[i].f
      Exp *target = compare_lval->GetTarget();

      Field *target_field = NULL;
      if (ExpFld *ntarget = target->IfFld()) {
        target_field = ntarget->GetField();
        target = ntarget->GetTarget();
      }

      bool include_target = false;

      if (target->IsDrf() || target->IsClobber()) {
        // make sure the target is used in pointer arithmetic.
        Exp *sanitize_target = Trace::SanitizeExp(target);
        if (sanitize_target) {
          if (arithmetic_list.Contains(sanitize_target))
            include_target = true;
        }
      }
      else if (target->IsIndex()) {
        include_target = true;
      }

      if (!include_target)
        continue;

      Exp *terminate_test = Exp::MakeEmpty();
      if (target_field)
        terminate_test = Exp::MakeFld(terminate_test, target_field);

      TerminatorInfo info(target, terminate_test, terminate_int);

      if (!terminators->Contains(info)) {
        terminators->PushBack(info);

        // also add a zero terminator test if this is scanning for a specific
        // character in what looks like a string buffer.
        long term_value;
        if (terminate_int->GetInt(&term_value) && term_value != 0 &&
            terminate_test->IsEmpty()) {
          ExpInt *zero_int = Exp::MakeInt(0);
          TerminatorInfo info(target, terminate_test, zero_int);

          if (!terminators->Contains(info))
            terminators->PushBack(info);
        }
      }
    }
  }
}

Bit* GetTerminatorInvariant(Type *stride_type, Exp *target, Exp *init_target,
                            Exp *terminate_test, ExpInt *terminate_int)
{
  Assert(stride_type);

  if (stride_type->Width() == 0)
    return NULL;

  // make an invariant test: (term(init_target) >= 0 ==> term(target) >= 0)

  Exp *terminate =
    Exp::MakeTerminate(target, stride_type, terminate_test, terminate_int);

  Exp *zero = Exp::MakeInt(0);
  Bit *base_test = Exp::MakeCompareBit(B_GreaterEqual, terminate, zero);

  Exp *init_terminate =
    Exp::MakeTerminate(init_target, stride_type, terminate_test, terminate_int);

  Bit *init_test = Exp::MakeCompareBit(B_GreaterEqual, init_terminate, zero);

  // get the final implication.
  return Bit::MakeImply(init_test, base_test);
}

NAMESPACE_XGILL_END
