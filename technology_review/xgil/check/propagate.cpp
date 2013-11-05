
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

#include "propagate.h"

#include "checker.h"
#include "sufficient.h"

#include <memory/baked.h>
#include <infer/expand.h>

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// CheckerPropagate
/////////////////////////////////////////////////////////////////////

CheckerPropagate::CheckerPropagate(CheckerFrame *frame,
                                   PPoint point, bool allow_point)
  : m_frame(frame), m_id(0), m_point(point), m_allow_point(allow_point),
    m_prefer_precondition(false), m_where(NULL),
    m_base_bit(NULL), m_point_bit(NULL)
{
  // try to do caller heap propagation regardless if we'll be expanding the
  // caller anyways.
  if (m_frame->GetCaller().id || m_frame->GetLoopParent().id ||
      m_frame->Kind() == B_Loop)
    m_prefer_precondition = true;
}

CheckerPropagate::~CheckerPropagate()
{
  if (m_where)
    delete m_where;
}

// ordering for which sufficient conditions we want to process first.
// try to pick conditions such that the first one in the ordering
// is most likely to succeed, and is easiest to check.
struct CompareSufficientPropagate
{
  static int Compare(CheckerPropagate *prop0, CheckerPropagate *prop1)
  {
    int res = Where::PriorityCompare(prop0->m_where, prop1->m_where);

    if (res && checker_verbose.IsSpecified()) {
      logout << "CHECK: Compared propagations: " << res << endl;
      prop0->Print();
      prop1->Print();
    }

    return res;
  }
};

void CheckerPropagate::SetBaseBit(Bit *base_bit, Bit *point_bit)
{
  Assert(!m_base_bit);
  Assert(!m_point_bit);

  m_base_bit = base_bit;
  m_point_bit = point_bit;

  Solver *solver = m_frame->State()->GetSolver();
  solver->GetBitTerms(m_frame->Id(), point_bit, &m_point_terms);
  SortVector< Exp*, SortObjectsCompare<Exp> >(&m_point_terms);
}

void CheckerPropagate::FindTest(Bit *base_bit, Bit *point_bit)
{
  SetBaseBit(base_bit, point_bit);

  // get the sufficient conditions we can use, if there are any.
  Vector<CheckerPropagate*> propagate_list;
  GetSufficientConditions(this, point_bit, &propagate_list);

  if (!propagate_list.Empty()) {
    // sort the propagations according to how much we like their directions.
    SortVector<CheckerPropagate*,CompareSufficientPropagate>(&propagate_list);

    // use the best direction we found in the sufficient conditions.
    m_where = propagate_list[0]->m_where;
    propagate_list[0]->m_where = NULL;

    for (size_t ind = 0; ind < propagate_list.Size(); ind++)
      delete propagate_list[ind];
  }
  else {
    // do what propagation we can based on the converted bit.
    SetTest(point_bit);
  }
}

// visitor for the initial pass over the bit used to determine propagation.
// this sees all subexpressions, not just lvalues.
class PropagateScanVisitor : public ExpVisitor
{
public:
  bool ignore;     // ignore this bit outright.
  bool has_frame;  // bit has frame terms from some caller.

  PropagateScanVisitor()
    : ExpVisitor(VISK_All), ignore(false), has_frame(false) {}

  void Visit(Exp *exp)
  {
    if (exp->IsFrame())
      has_frame = true;

    if (ExpFld *nexp = exp->IfFld()) {
      Field *field = nexp->GetField();

      if (IgnoreField(field))
        ignore = true;
    }
  }
};

void CheckerPropagate::SetTest(Bit *safe_bit)
{
  Assert(!m_where);

  Vector<Exp*> safe_terms;

  Solver *solver = m_frame->State()->GetSolver();
  solver->GetBitTerms(m_frame->Id(), safe_bit, &safe_terms);
  SortVector< Exp*, SortObjectsCompare<Exp> >(&safe_terms);

  // setup the initial where info in a pass over the whole bit. the bit might
  // be outright ignored or we might be forced to go to the caller because
  // of an ExpFrame subexpression.
  PropagateScanVisitor visitor;
  safe_bit->DoVisit(&visitor);

  if (visitor.ignore)
    m_where = new WhereNone(RK_None);
  else if (visitor.has_frame)
    m_where = WherePrecondition::Make(m_frame->Memory(), safe_bit);

  // try to find a direction which accomodates all terms in the bit.
  for (size_t ind = 0; ind < safe_terms.Size(); ind++) {
    Where *new_where = TryPropagate(safe_bit, safe_terms[ind]);

    if (new_where) {
      if (m_where) {
        // replace with the new direction only if it has higher priority.
        int priority = Where::PriorityCompare(new_where, m_where);
        if (priority < 0) {
          delete m_where;
          m_where = new_where;
        }
        else {
          delete new_where;
        }
      }
      else {
        m_where = new_where;
      }
    }
  }

  if (!m_where) {
    if (!safe_terms.Empty()) {
      // couldn't find a way to propagate from this point, generate Unexpected.
      m_where = new WhereNone(RK_Unexpected);
    }
    else {
      // nowhere to go from here.
      m_where = new WhereNone(RK_Finished);
    }
  }
}

Where* CheckerPropagate::TryPropagate(Bit *bit, Exp *lval)
{
  BlockMemory *mcfg = m_frame->Memory();

  TypeCSU *csu = NULL;
  Exp *csu_lval = NULL;

  if (UseHeapExp(lval, &csu, &csu_lval)) {
    // do the heap propagation unless we are trying to push heap data
    // up into the caller.
    if (!m_prefer_precondition ||
        !UseCallerExp(lval, m_frame->Kind() == B_Function) ||
        (m_frame->Kind() == B_Loop && !mcfg->IsExpPreserved(lval))) {
      Where *res = WhereInvariant::Make(csu, csu_lval, bit);

      if (res)
        return res;

      // fall through, we might still be able to treat this as a precondition.
    }
  }

  if (UseCallerExp(lval, m_frame->Kind() == B_Function))
    return WherePrecondition::Make(m_frame->Memory(), bit);

  if (PPoint point = UseCalleeExp(lval)) {

    // fail propagation if this is from a later callee than the point
    // this propagation occurs at. this can come up when generating
    // sufficient conditions.
    if (point > m_point || (point == m_point && !m_allow_point))
      return NULL;

    // cutoff propagation if the buffer came from a primitive memory
    // allocator. if we find a sufficient condition that does not
    // mention the allocator we could continue propagation.

    PEdge *edge = mcfg->GetCFG()->GetSingleOutgoingEdge(point);
    PEdgeCall *edge_call = edge->IfCall();
    Variable *callee = edge_call ? edge_call->GetDirectFunction() : NULL;

    Exp *callee_base;
    Exp *callee_size;

    if (callee && GetAllocationFunction(callee, &callee_base, &callee_size)) {
      if (lval->IsBound())
        lval = lval->GetLvalTarget();

      // ignore this if it refers to fields or other structures
      // in the result of the allocation. this data is either
      // uninitialized or zeroed, either way we don't care.
      if (ExpClobber *nlval = lval->IfClobber()) {
        Exp *callee_lval = nlval->GetCallee();
        Exp *callee_target = NULL;

        if (nlval->GetValueKind() == NULL) {
          callee_target = callee_lval;
        }
        else {
          // skip the first dereference. for terminators we still depend on
          // the initial contents of the allocated buffer.
          if (ExpExit *ncallee = callee_lval->IfExit())
            callee_target = ncallee->GetTarget();
        }

        if (callee_target) {
          while (callee_target->IsFld())
            callee_target = callee_target->GetLvalTarget();
          if (callee_target->IsExit())
            return new WhereNone(RK_None);
        }
      }

      // watch for accessing indexes of a buffer returned via the allocator,
      // which currently aren't mapped back into the callee correctly.
      // TODO: fix hack.
      if (lval->IsDrf() && lval->GetLvalTarget()->IsIndex())
        return new WhereNone(RK_None);

      return new WhereNone(RK_Finished);
    }

    if (callee && IsCutoffFunction(callee))
      return new WhereNone(RK_Finished);

    return WherePostcondition::Make(m_frame, point, bit);
  }

  return NULL;
}

void CheckerPropagate::Print()
{
  logout << "Propagate: frame " << m_frame << ", point: " << m_point;

  if (m_allow_point)
    logout << " [allow_point]";
  if (m_prefer_precondition)
    logout << " [prefer_precondition]";
  logout << endl;

  if (m_base_bit)
    logout << "  base " << m_base_bit << endl;

  if (m_point_bit)
    logout << "  point " << m_point_bit << endl;

  if (m_where)
    logout << "  where " << m_where << endl;
}

NAMESPACE_XGILL_END
