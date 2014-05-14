
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

#include "modset.h"
#include "serial.h"
#include "mstorage.h"
#include "baked.h"

NAMESPACE_XGILL_BEGIN

// cutoff for how large expressions in modset assignments can get.
#define ASSIGN_EXP_CUTOFF 10

// cutoff for how large bits in modset assignments can get.
#define ASSIGN_BIT_CUTOFF 20

/////////////////////////////////////////////////////////////////////
// BlockModset static
/////////////////////////////////////////////////////////////////////

HashCons<BlockModset> BlockModset::g_table;

int BlockModset::Compare(const BlockModset *mod0, const BlockModset *mod1)
{
  BlockId *id0 = mod0->GetId();
  BlockId *id1 = mod1->GetId();
  TryCompareObjects(id0, id1, BlockId);
  return 0;
}

BlockModset* BlockModset::Copy(const BlockModset *mod)
{
  return new BlockModset(*mod);
}

void BlockModset::Write(Buffer *buf, const BlockModset *mod)
{
  WriteOpenTag(buf, TAG_BlockModset);
  BlockId::Write(buf, mod->GetId());

  for (size_t ind = 0; ind < mod->GetModsetCount(); ind++) {
    const PointValue &v = mod->m_modset_list->At(ind);

    WriteOpenTag(buf, TAG_ModsetEntry);
    Exp::Write(buf, v.lval);
    if (v.kind)
      Exp::Write(buf, v.kind);
    WriteCloseTag(buf, TAG_ModsetEntry);
  }

  for (size_t ind = 0; ind < mod->GetAssignCount(); ind++) {
    const GuardAssign &v = mod->m_assign_list->At(ind);
    Assert(v.kind == NULL);

    WriteOpenTag(buf, TAG_ModsetAssign);
    Exp::Write(buf, v.left);
    Exp::Write(buf, v.right);
    Bit::Write(buf, v.guard);
    WriteCloseTag(buf, TAG_ModsetAssign);
  }

  if (mod->CanGC())
    WriteTagEmpty(buf, TAG_ModsetCanGC);

  WriteCloseTag(buf, TAG_BlockModset);
}

BlockModset* BlockModset::Read(Buffer *buf)
{
  BlockModset *res = NULL;

  Try(ReadOpenTag(buf, TAG_BlockModset));
  while (!ReadCloseTag(buf, TAG_BlockModset)) {
    switch (PeekOpenTag(buf)) {
    case TAG_BlockId: {
      Try(!res);
      BlockId *id = BlockId::Read(buf);
      res = Make(id);

      // clear out the modset in case it was in memory so we don't add the
      // same entries multiple times.
      res->ClearModset();
      break;
    }
    case TAG_ModsetCanGC: {
      res->SetCanGC();
      Try(ReadTagEmpty(buf, TAG_ModsetCanGC));
      break;
    }
    case TAG_ModsetEntry: {
      Try(res);

      Try(ReadOpenTag(buf, TAG_ModsetEntry));
      Exp *lval = Exp::Read(buf);
      Exp *kind = NULL;
      if (PeekOpenTag(buf) == TAG_Exp)
        kind = Exp::Read(buf);
      Try(ReadCloseTag(buf, TAG_ModsetEntry));

      res->AddModset(lval, kind);
      break;
    }
    case TAG_ModsetAssign: {
      Try(res);

      Try(ReadOpenTag(buf, TAG_ModsetAssign));
      Exp *left = Exp::Read(buf);
      Exp *right = Exp::Read(buf);
      Bit *guard = Bit::Read(buf);
      Try(ReadCloseTag(buf, TAG_ModsetAssign));

      res->AddAssign(left, right, guard);
      break;
    }
    default:
      Try(false);
    }
  }

  Try(res);
  return res;
}

void BlockModset::WriteList(Buffer *buf, const Vector<BlockModset*> &mods)
{
  Assert(buf->pos == buf->base);
  for (size_t ind = 0; ind < mods.Size(); ind++)
    Write(buf, mods[ind]);
}

void BlockModset::ReadList(Buffer *buf, Vector<BlockModset*> *mods)
{
  Assert(buf->pos == buf->base);

  while (buf->pos != buf->base + buf->size) {
    BlockModset *mod;
    Try(mod = Read(buf));
    mods->PushBack(mod);
  }
}

/////////////////////////////////////////////////////////////////////
// BlockModset
/////////////////////////////////////////////////////////////////////

BlockModset::BlockModset(BlockId *id)
  : m_id(id), m_modset_list(NULL), m_assign_list(NULL), m_can_gc(false)
{
  Assert(m_id);
  m_hash = m_id->Hash();
}

void BlockModset::ClearModset()
{
  if (m_modset_list) {
    delete m_modset_list;
    m_modset_list = NULL;
  }

  if (m_assign_list) {
    delete m_assign_list;
    m_assign_list = NULL;
  }

  m_can_gc = false;
}

struct compare_PointValue
{
  static int Compare(const PointValue &lval0, const PointValue &lval1)
  {
    Assert(lval0.point == 0);
    Assert(lval1.point == 0);
    if (lval0.lval != lval1.lval)
      return Exp::Compare(lval0.lval, lval1.lval);
    if (lval0.kind != lval1.kind) {
      if (!lval0.kind)
        return -1;
      if (!lval1.kind)
        return 1;
      return Exp::Compare(lval0.kind, lval1.kind);
    }
    return 0;
  }
};

struct compare_GuardAssign
{
  static int Compare(const GuardAssign &gasn0, const GuardAssign &gasn1)
  {
    Assert(gasn0.kind == NULL);
    Assert(gasn1.kind == NULL);
    if (gasn0.left != gasn1.left)
      return Exp::Compare(gasn0.left, gasn1.left);
    if (gasn0.right != gasn1.right)
      return Exp::Compare(gasn0.right, gasn1.right);
    return Bit::Compare(gasn0.guard, gasn1.guard);
  }
};

void BlockModset::ComputeModset(BlockMemory *mcfg, bool indirect)
{
  static BaseTimer compute_timer("modset_compute");
  Timer _timer(&compute_timer);

  // get any indirect callees for this function, provided they have been
  // computed and stored in the callee database (indirect is set).
  CallEdgeSet *indirect_callees = NULL;
  if (indirect)
    indirect_callees = CalleeCache.Lookup(m_id->BaseVar());

  BlockCFG *cfg = mcfg->GetCFG();
  for (size_t eind = 0; eind < cfg->GetEdgeCount(); eind++) {
    PEdge *edge = cfg->GetEdge(eind);
    PPoint point = edge->GetSource();

    if (edge->IsAssign() || edge->IsCall()) {
      // process direct assignments along this edge.

      const Vector<GuardAssign>* assigns = mcfg->GetAssigns(point);
      if (assigns) {
        for (size_t aind = 0; aind < assigns->Size(); aind++) {
          const GuardAssign &gasn = assigns->At(aind);
          ProcessUpdatedLval(mcfg, gasn.left, NULL, true, false);

          Exp *use_lval = NULL;
          Exp *kind = mcfg->GetTerminateAssign(point, gasn.left, gasn.right,
                                               &use_lval);
          if (kind)
            ProcessUpdatedLval(mcfg, use_lval, kind, false, false);
        }
      }
    }

    // pull in modsets from the direct and indirect callees of the edge.
    if (BlockId *callee = edge->GetDirectCallee()) {
      ComputeModsetCall(mcfg, edge, callee, NULL);
    }
    else if (edge->IsCall() && indirect_callees) {
      for (size_t ind = 0; ind < indirect_callees->GetEdgeCount(); ind++) {
        const CallEdge &cedge = indirect_callees->GetEdge(ind);

        // when comparing watch out for the case that this is a temporary
        // modset and does not share the same block kind as the edge point.
        if (cedge.where.version == cfg->GetVersion() &&
            cedge.where.point == point &&
            cedge.where.id->Function() == m_id->Function() &&
            cedge.where.id->Loop() == m_id->Loop()) {
          BlockId *callee = BlockId::Make(B_Function, cedge.callee);
          ComputeModsetCall(mcfg, edge, callee, cedge.rfld_chain);
        }
      }
    }
  }

  // sort the modset exps to ensure a consistent representation.
  if (m_modset_list)
    SortVector<PointValue,compare_PointValue>(m_modset_list);
  if (m_assign_list)
    SortVector<GuardAssign,compare_GuardAssign>(m_assign_list);

  // seed may-GC information.
  if (!strcmp(m_id->BaseVar()->GetSourceName()->Value(), "js_GC"))
    SetCanGC();

  if (indirect)
    CalleeCache.Release(m_id->BaseVar());
}

void BlockModset::ComputeModsetCall(BlockMemory *mcfg, PEdge *edge,
                                    BlockId *callee, Exp *rfld_chain)
{
  PPoint point = edge->GetSource();
  BlockModset *modset = GetBlockModset(callee);

  for (size_t mind = 0; mind < modset->GetModsetCount(); mind++) {
    const PointValue &cv = modset->GetModsetLval(mind);
    Exp *new_lval = CallEdgeAddRfldExp(cv.lval, callee, rfld_chain);

    GuardExpVector caller_res;
    mcfg->TranslateExp(TRK_Callee, point, new_lval, &caller_res);

    for (size_t cind = 0; cind < caller_res.Size(); cind++) {
      const GuardExp &gt = caller_res[cind];
      ProcessUpdatedLval(mcfg, gt.exp, cv.kind, false, edge->IsCall());
    }
  }

  if (modset->CanGC() && !BlockCannotGC(m_id)) {
    logout << "Callee can GC: " << callee << endl;
    SetCanGC();
  }
}

bool BlockModset::MergeModset(BlockModset *omod)
{
  for (size_t ind = 0; ind < omod->GetModsetCount(); ind++) {
    const PointValue &olv = omod->GetModsetLval(ind);

    if (!m_modset_list)
      m_modset_list = new Vector<PointValue>();

    if (!m_modset_list->Contains(olv))
      m_modset_list->PushBack(olv);
  }

  for (size_t ind = 0; ind < omod->GetAssignCount(); ind++) {
    const GuardAssign &ogasn = omod->GetAssign(ind);

    if (!m_assign_list)
      m_assign_list = new Vector<GuardAssign>();

    if (!m_assign_list->Contains(ogasn))
      m_assign_list->PushBack(ogasn);
  }

  // resort the modset contents.
  if (m_modset_list)
    SortVector<PointValue,compare_PointValue>(m_modset_list);
  if (m_assign_list)
    SortVector<GuardAssign,compare_GuardAssign>(m_assign_list);

  if (omod->CanGC())
    SetCanGC();

  // check if this modset is bigger than omod. since everything in omod is
  // also in this modset, this will determine if the two are different.
  if (GetModsetCount() != omod->GetModsetCount())
    return true;
  if (GetAssignCount() != omod->GetAssignCount())
    return true;
  if (CanGC() && !omod->CanGC())
    return true;
  return false;
}

void BlockModset::AddModset(Exp *lval, Exp *kind)
{
  if (!m_modset_list)
    m_modset_list = new Vector<PointValue>();

  PointValue value(lval, kind, 0);

  if (!m_modset_list->Contains(value))
    m_modset_list->PushBack(value);
}

void BlockModset::AddAssign(Exp *left, Exp *right, Bit *guard)
{
  if (!m_assign_list)
    m_assign_list = new Vector<GuardAssign>();

  GuardAssign assign(left, right, guard);

  if (!m_assign_list->Contains(assign))
    m_assign_list->PushBack(assign);
}

void BlockModset::Print(OutStream &out) const
{
  out << "modset: " << m_id << endl;

  for (size_t ind = 0; ind < GetAssignCount(); ind++) {
    const GuardAssign &v = m_assign_list->At(ind);
    out << "  " << v.left << " := " << v.right << " " << v.guard << endl;
  }

  for (size_t ind = 0; ind < GetModsetCount(); ind++) {
    const PointValue &v = m_modset_list->At(ind);
    out << "  mod " << v.lval;
    if (v.kind)
      out << " [" << v.kind << "]";
    out << endl;
  }

  if (CanGC())
    out << "  canGC" << endl;
}

void BlockModset::MarkChildren() const
{
  m_id->Mark();

  if (m_modset_list) {
    for (size_t ind = 0; ind < m_modset_list->Size(); ind++) {
      const PointValue &v = m_modset_list->At(ind);
      v.lval->Mark();
      if (v.kind)
        v.kind->Mark();
    }
  }

  if (m_assign_list) {
    for (size_t ind = 0; ind < m_assign_list->Size(); ind++) {
      const GuardAssign &v = m_assign_list->At(ind);
      v.left->Mark();
      v.right->Mark();
      v.guard->Mark();
    }
  }
}

void BlockModset::Persist()
{
  Assert(m_modset_list == NULL);
  Assert(m_assign_list == NULL);
}

void BlockModset::UnPersist()
{
  delete m_modset_list;
  delete m_assign_list;
}

class ModsetIncludeVisitor : public ExpVisitor
{
 public:
  // kind of block we are generating a modset for.
  BlockKind kind;

  // whether this modset data was propagated out from a function call.
  // we include globals in the modset only when they were directly modified.
  bool from_call;

  // encountered an lval which should be excluded from generated information.
  Exp *excluded;

  // whether we are scanning a buffer term for a terminator lvalue.
  bool buffer;

  // whether we are scanning the rvalue for an assignment.
  bool rvalue;

  ModsetIncludeVisitor(BlockKind _kind, bool _from_call)
    : ExpVisitor(VISK_All),
      kind(_kind), from_call(_from_call), excluded(NULL),
      buffer(false), rvalue(false)
  {}

  void Visit(Exp *exp)
  {
    if (exp->IsVar()) {
      Variable *root = exp->AsVar()->GetVariable();

      // allow global exps when the assign was not generated from a call.
      if (root->IsGlobal() && (!from_call || rvalue))
        return;

      if (kind == B_Function) {
        // only consider exps derived from arguments, 'this' and the return
        // variable. note that we will special case the return var later in the
        // modset as it is automatically handled by BlockMemory, but we don't
        // exclude it here so that we can get exact side effects for it
        // if possible.
        if (root->Kind() != VK_Arg &&
            root->Kind() != VK_This &&
            root->Kind() != VK_Return)
          excluded = exp;

        // watch for taking the address of function arguments and leaving them
        // accessible in the caller. weird!
        if (root->Kind() == VK_Arg && !FoundLval())
          excluded = exp;
      }
      else {
        // only consider exps derived from arguments, 'this' and locals.
        if (root->Kind() != VK_Arg &&
            root->Kind() != VK_This &&
            root->Kind() != VK_Local)
          excluded = exp;
      }

      return;
    }

    if (exp->IsDrf()) {
      if (!FoundLval())
        return;

      if (!rvalue) {
        // limits on the number of dereferences in expressions.
        size_t max_derefs = buffer ? 2 : 1;
        if (exp->DrfCount() > max_derefs)
          excluded = exp;
      }

      return;
    }

    if (exp->IsIndex() && !rvalue) {
      // indexes are allowed only for assignment rvalues.
      excluded = exp;
      return;
    }

    if (exp->IsFld() && exp->FldCount() > 6) {
      // limit on the number of fields in expressions. this cuts off infinite
      // recursion during modset computation when the program does funny casts.
      excluded = exp;
      return;
    }

    if (exp->IsRfld()) {
      // all rfld expressions are excluded. these are usually here because
      // of indirect calls which could operate on a variety of structures
      // (this happens in both C and C++).
      excluded = exp;
      return;
    }

    if (exp->IsClobber() || exp->IsVal()) {
      excluded = exp;
      return;
    }
  }
};

void BlockModset::ProcessUpdatedLval(BlockMemory *mcfg, Exp *lval, Exp *kind,
                                     bool consider_assign, bool from_call)
{
  if (!m_modset_list)
    m_modset_list = new Vector<PointValue>();
  if (!m_assign_list)
    m_assign_list = new Vector<GuardAssign>();

  // use the ID from the memory rather than the ID from this modset,
  // as this modset has a temporary ID.
  BlockId *use_id = mcfg->GetId();

  ModsetIncludeVisitor visitor(use_id->Kind(), from_call);

  // use the base buffer if we are updating a terminator.
  if (kind) {
    if (ExpTerminate *nkind = kind->IfTerminate()) {
      // ignore field terminator modsets, these are pretty much useless.
      if (nkind->GetTerminateTest()->IsFld())
        return;

      lval = mcfg->GetBaseBuffer(lval, nkind->GetStrideType());
      visitor.buffer = true;
    }
  }

  visitor.SetFoundLval(true);
  lval->DoVisit(&visitor);
  visitor.SetFoundLval(false);

  visitor.rvalue = true;

  if (visitor.excluded)
    return;

  Variable *root = lval->Root();
  if (!root)
    return;

  // argument lvals with zero dereferences are additionally excluded.
  // these updates are local to the current function. also look for updates
  // to 'this' which can come from frontend parse/tcheck errors.
  if (use_id->Kind() == B_Function &&
      (root->Kind() == VK_Arg || root->Kind() == VK_This)) {
    if (lval->DrfCount() == 0)
      return;
  }

  // add to the modset if this is not the function's return value. we don't
  // need to explicitly add the return value as it is special cased by
  // BlockMemory and is always treated as modified.
  if (root->Kind() != VK_Return)
    AddModset(lval, kind);

  if (!consider_assign)
    return;

  // should only be generating direct assignments for Drf() updates.
  Assert(kind == NULL);

  // don't generate assignments for loop iterations.
  if (use_id->Kind() != B_Function)
    return;

  // don't generate assignments for global variables.
  if (root->IsGlobal())
    return;

  // see if we already have assignments for this lval.
  for (size_t ind = 0; ind < GetAssignCount(); ind++) {
    if (m_assign_list->At(ind).left == lval)
      return;
  }

  PPoint exit_point = mcfg->GetCFG()->GetExitPoint();
  if (!exit_point)
    return;

  // temporary vector to hold assignments. if we find a problem with
  // the assigns (bad lvalue, etc.) we will bail out and clear this list.
  Vector<GuardAssign> assigns;

  GuardExpVector exit_values;
  mcfg->GetValComplete(lval, NULL, exit_point, &exit_values, true);

  // cases we will currently generate assignments for. in all cases
  // the rvalue and guard must be functionally determined from the arguments.
  // 1. one or two possible values for the lval.
  // 2. all values for the lval are constants.

  for (size_t ind = 0; ind < exit_values.Size(); ind++) {
    const GuardExp &val = exit_values[ind];

    if (val.guard->Size() >= ASSIGN_BIT_CUTOFF)
      return;

    if (exit_values.Size() <= 2) {
      if (val.exp->TermCountExceeds(ASSIGN_EXP_CUTOFF))
        return;
    }
    else {
      if (!val.exp->IsInt())
        return;
    }
  }

  for (size_t ind = 0; ind < exit_values.Size(); ind++) {
    const GuardExp &val = exit_values[ind];
    val.exp->DoVisit(&visitor);
    val.guard->DoVisit(&visitor);
    assigns.PushBack(GuardAssign(lval, val.exp, val.guard));
  }

  if (!visitor.excluded) {
    for (size_t ind = 0; ind < assigns.Size(); ind++) {
      const GuardAssign &gasn = assigns[ind];
      AddAssign(gasn.left, gasn.right, gasn.guard);
    }
  }
}

NAMESPACE_XGILL_END
