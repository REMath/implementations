
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

#include "expand.h"

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// Caller functions
/////////////////////////////////////////////////////////////////////

// determine whether an expression can be expanded in its callers.
class ExternalVisitor : public ExpVisitor
{
public:
  bool is_function;  // whether this is for a function vs. loop.
  bool exclude;

  ExternalVisitor(bool _is_function)
    : ExpVisitor(VISK_All), is_function(_is_function), exclude(false)
  {}

  void Visit(Exp *exp)
  {
    if (exp->IsVar()) {
      Variable *var = exp->AsVar()->GetVariable();

      if (var->IsGlobal())
        return;

      if (is_function) {
        // arguments for functions are only allowed in an lval context,
        // i.e. the outer scalar does not refer just to the address of
        // a call-by-value argument.
        if (var->Kind() == VK_Arg && FoundLval())
          return;
        if (var->Kind() == VK_This || var->Kind() == VK_Return)
          return;
      }
      else {
        if (var->Kind() != VK_Temp)
          return;
      }

      exclude = true;
      return;
    }

    if (exp->IsClobber() || exp->IsVal()) {
      exclude = true;
      return;
    }

    if (exp->IsInitial() && is_function) {
      if (is_function)
        exclude = true;
      return;
    }

    if (exp->IsGCSafe() && !exp->AsGCSafe()->GetTarget()) {
      exclude = true;
      return;
    }
  }
};

bool UseCallerExp(Exp *exp, bool is_function)
{
  ExternalVisitor visitor(is_function);
  exp->DoVisit(&visitor);
  return !visitor.exclude;
}

bool UseCallerBit(Bit *bit, bool is_function)
{
  ExternalVisitor visitor(is_function);
  bit->DoVisit(&visitor);
  return !visitor.exclude;
}

/////////////////////////////////////////////////////////////////////
// Callee functions
/////////////////////////////////////////////////////////////////////

// mapper to normalize variables used as the callee expressions in a cval.
// TODO: move this into modset computation.
class NormalizeCalleeMapper : public ExpMapper
{
 public:
  NormalizeCalleeMapper()
    : ExpMapper(VISK_SubExprs, WIDK_Drop)
  {}

  Exp* Map(Exp *exp, Exp *old)
  {
    Assert(exp);

    if (ExpVar *nexp = exp->IfVar()) {
      // remove block/name information for arguments.
      Variable *var = nexp->GetVariable();

      if (var->Kind() == VK_Arg) {
        Variable *new_var = Variable::Make(NULL, VK_Arg,
                                           NULL, var->GetIndex(), NULL);
        return Exp::MakeVar(new_var);
      }
    }

    return exp;
  }
};


class CalleeMapper : public ExpMapper
{
 public:
  // memory of the block we are mapping into the callees of.
  BlockMemory *mcfg;

  // point is zero if we don't know what point the callee is at,
  // and will be filled in when a callee clobbered lval is encountered.
  PPoint point;

  // frame for the caller for generating ExpFrame values on exps
  // we can't convert into the callee scope. 0 if we should just return NULL
  // when we can't do the conversion.
  FrameId caller_frame_id;

  CalleeMapper(BlockMemory *_mcfg, PPoint _point, FrameId _caller_frame_id)
    : ExpMapper(VISK_All, WIDK_Drop),
      mcfg(_mcfg), point(_point), caller_frame_id(_caller_frame_id)
  {}

  Exp* Map(Exp *exp, Exp *old)
  {
    if (exp == NULL)
      goto exit;

    // don't map expressions built on an ExpFrame.
    if (Exp *target = exp->GetLvalTarget()) {
      if (target->IsFrame())
        goto exit;
    }

    // handle the results of lvalues clobbered by the callee.
    if (ExpClobber *nexp = exp->IfClobber()) {
      PPoint clobber_point = nexp->GetPoint();

      if (point == 0)
        point = clobber_point;

      if (point != clobber_point)
        goto exit;

      Exp *callee = nexp->GetCallee();
      Exp *value_kind = nexp->GetValueKind();

      // use the normalized names for arguments, etc. except for loops.
      // TODO: this should really be pushed up into the modset computation.
      Exp *new_callee = NULL;

      if (mcfg && point && !mcfg->GetCFG()->PointEdgeIsCall(point)) {
        new_callee = callee;
      }
      else {
        NormalizeCalleeMapper callee_mapper;
        new_callee = callee->DoMap(&callee_mapper);
      }

      return Exp::MakeExit(new_callee, value_kind);
    }

    if (ExpVar *nexp = exp->IfVar()) {
      // we can map any variable back into a loop callee, and global variables
      // back into any callee.
      Variable *var = nexp->GetVariable();

      // only try to map variables if we already have a point, i.e. we are not
      // just probing to see which callee a subexpression of a bit should go.
      if (mcfg && point) {
        if (var->IsGlobal())
          return exp;
        if (!mcfg->GetCFG()->PointEdgeIsCall(point))
          return exp;
      }

      goto exit;
    }

    if (ExpTerminate *nexp = exp->IfTerminate()) {
      // map terminate expressions using Exit expressions to account for
      // changes in terminator position by the callee.
      Exp *target = nexp->GetTarget();

      Exp *value_kind = exp->ReplaceLvalTarget(NULL);
      return Exp::MakeExit(target, value_kind);
    }

    // other expressions can be handled as is.
    if (exp->IsLvalue() || exp->IsRvalue())
      return exp;

  exit:
    // we don't have a callee representation of the expression.

    // see if we can map this into the callee as a function argument.
    if (mcfg && point) {
      const Vector<GuardAssign> *arguments = mcfg->GetArguments(point);
      if (arguments) {
        for (size_t ind = 0; ind < arguments->Size(); ind++) {
          const GuardAssign &gasn = arguments->At(ind);
          if (gasn.right == old && gasn.guard->IsTrue())
            return Exp::MakeDrf(gasn.left);
        }
      }
    }

    if (old->IsFrame())
      return old;

    return Exp::MakeFrame(old, caller_frame_id);
  }
};

PPoint UseCalleeExp(Exp *exp)
{
  CalleeMapper mapper(NULL, 0, 0);
  Exp *res = exp->DoMap(&mapper);

  bool useful = res ? !res->IsFrame() : false;

  if (useful && mapper.point)
    return mapper.point;
  return 0;
}

Exp* TranslateCalleeExp(BlockMemory *mcfg, PPoint point, Exp *exp,
                        FrameId caller_frame_id)
{
  CalleeMapper mapper(mcfg, point, caller_frame_id);
  return exp->DoMap(&mapper);
}

Bit* TranslateCalleeBit(BlockMemory *mcfg, PPoint point, Bit *bit,
                        FrameId caller_frame_id)
{
  CalleeMapper mapper(mcfg, point, caller_frame_id);
  return bit->DoMap(&mapper);
}

/////////////////////////////////////////////////////////////////////
// Heap functions
/////////////////////////////////////////////////////////////////////

bool UseHeapExp(Exp *exp, TypeCSU **pcsu, Exp **pcsu_lval)
{
  if (exp->IsBound() || exp->IsTerminate() || exp->IsNullTest())
    exp = exp->GetLvalTarget();

  if (Exp *target = ExpDereference(exp)) {
    // only dereferenced lvalues we are handling for heap writes are
    // plain global variables and plain fields.

    if (ExpVar *ntarget = target->IfVar()) {
      if (ntarget->GetVariable()->IsGlobal())
        return true;
    }

    if (ExpFld *ntarget = target->IfFld()) {
      TypeCSU *csu = ntarget->GetField()->GetCSUType();
      *pcsu = csu;

      Exp *new_target = ntarget->GetTarget();
      *pcsu_lval = new_target;

      return true;
    }
  }

  return false;
}

class HeapMapper : public ExpMapper
{
 public:
  Exp *old_lval;
  Exp *new_lval;
  bool use_exit;

  HeapMapper(Exp *_old_lval, Exp *_new_lval, bool _use_exit)
    : ExpMapper(VISK_All, WIDK_Drop),
      old_lval(_old_lval), new_lval(_new_lval), use_exit(_use_exit)
  {}

  Exp* Map(Exp *exp, Exp *old)
  {
    if (old == old_lval)
      return new_lval;

    if (exp == NULL)
      return NULL;

    // global variables are the same in all scopes.
    if (ExpVar *nexp = exp->IfVar()) {
      if (nexp->GetVariable()->IsGlobal())
        return exp;
    }

    if (use_exit) {
      if (ExpDrf *nexp = exp->IfDrf()) {
        Exp *target = nexp->GetTarget();
        return Exp::MakeExit(target, NULL);
      }

      if (ExpTerminate *nexp = exp->IfTerminate()) {
        Exp *target = nexp->GetTarget();
        Exp *kind = exp->ReplaceLvalTarget(NULL);
        return Exp::MakeExit(target, kind);
      }
    }

    if (exp->IsClobber())
      return NULL;

    if (exp->IsRvalue() || exp->IsDrf() ||
        exp->IsFld() || exp->IsRfld() || exp->IsIndex())
      return exp;

    return NULL;
  }
};

Exp* TranslateHeapExp(Exp *old_lval, Exp *new_lval, bool use_exit, Exp *exp)
{
  HeapMapper mapper(old_lval, new_lval, use_exit);
  return exp->DoMap(&mapper);
}

Bit* TranslateHeapBit(Exp *old_lval, Exp *new_lval, bool use_exit, Bit *bit)
{
  HeapMapper mapper(old_lval, new_lval, use_exit);
  return bit->DoMap(&mapper);
}

Exp* ConvertCallsiteMapper::Map(Exp *value, Exp *old)
{
  // strip Initial expressions if we're not unrolling a loop iteration.
  if (!unrolling) {
    if (ExpInitial *nvalue = value->IfInitial()) {
      Exp *target = nvalue->GetTarget();

      if (Exp *kind = nvalue->GetValueKind())
        return kind->ReplaceLvalTarget(target);
      return Exp::MakeDrf(target);
    }
  }

  if (!value->IsDrf())
    return value;

  if (point == cfg->GetExitPoint()) {
    // converting at the 'callsite' between adjacent loop iterations.
    return value;
  }

  PEdgeCall *edge = cfg->GetSingleOutgoingEdge(point)->IfCall();

  if (!edge) {
    // converting at a loop summary site.
    return value;
  }

  // see if we are converting a *arg at a callsite, in the same fashion
  // as in BlockMemory::TranslateExp.
  Exp *target = value->AsDrf()->GetTarget();

  // the target is an argument expression if it is rooted at an argument
  // and contains no dereferences.
  bool call_argument = false;
  size_t argument_index = 0;

  // the target is the 'this' expression.
  bool call_this = false;

  if (target->DrfCount() == 0) {
    Variable *root = target->Root();
    if (root) {
      if (root->Kind() == VK_Arg) {
        call_argument = true;
        argument_index = root->GetIndex();
      }
      if (root->Kind() == VK_This) {
        Assert(target->IsVar());
        call_this = true;
      }
    }
  }

  if (call_argument) {
    if (argument_index < edge->GetArgumentCount())
      return edge->GetArgument(argument_index);
    return Exp::MakeInt(0);
  }

  if (call_this) {
    if (Exp *object = edge->GetInstanceObject())
      return object;
    return Exp::MakeInt(0);
  }

  return value;
}

NAMESPACE_XGILL_END
