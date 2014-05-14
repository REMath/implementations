
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

#include "summary.h"
#include "serial.h"
#include "mstorage.h"
#include <imlang/loopsplit.h>
#include <imlang/storage.h>

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// BlockSummary static
/////////////////////////////////////////////////////////////////////

HashCons<BlockSummary> BlockSummary::g_table;

int BlockSummary::Compare(const BlockSummary *sum0, const BlockSummary *sum1)
{
  TryCompareObjects(sum0->GetId(), sum1->GetId(), BlockId);
  return 0;
}

BlockSummary* BlockSummary::Copy(const BlockSummary *sum)
{
  return new BlockSummary(*sum);
}

void BlockSummary::Write(Buffer *buf, const BlockSummary *sum)
{
  WriteOpenTag(buf, TAG_BlockSummary);
  BlockId::Write(buf, sum->GetId());

  size_t assert_count = VectorSize<AssertInfo>(sum->m_assert_list);
  for (size_t ind = 0; ind < assert_count; ind++) {
    const AssertInfo &info = sum->m_assert_list->At(ind);

    WriteOpenTag(buf, TAG_SummaryAssert);
    WriteTagUInt32(buf, TAG_Kind, info.kind);
    WriteTagUInt32(buf, TAG_OpCode, info.cls);
    WriteTagUInt32(buf, TAG_Index, info.point);
    Bit::Write(buf, info.bit);
    WriteCloseTag(buf, TAG_SummaryAssert);
  }

  size_t assume_count = VectorSize<Bit*>(sum->m_assume_list);
  for (size_t ind = 0; ind < assume_count; ind++) {
    WriteOpenTag(buf, TAG_SummaryAssume);
    Bit::Write(buf, sum->m_assume_list->At(ind));
    WriteCloseTag(buf, TAG_SummaryAssume);
  }

  WriteCloseTag(buf, TAG_BlockSummary);
}

BlockSummary* BlockSummary::Read(Buffer *buf)
{
  BlockSummary *res = NULL;

  Try(ReadOpenTag(buf, TAG_BlockSummary));
  while (!ReadCloseTag(buf, TAG_BlockSummary)) {
    switch (PeekOpenTag(buf)) {

    case TAG_BlockId: {
      Try(!res);
      BlockId *id = BlockId::Read(buf);
      res = Make(id);

      // we don't need to unpersist or drop the data we will be reading in.
      // if there is already a summary structure created, the adds we make
      // will just be ignored.
      break;
    }

    case TAG_SummaryAssert: {
      Try(res);
      uint32_t kind, cls;
      PPoint point;

      Try(ReadOpenTag(buf, TAG_SummaryAssert));
      Try(ReadTagUInt32(buf, TAG_Kind, &kind));
      Try(ReadTagUInt32(buf, TAG_OpCode, &cls));
      Try(ReadTagUInt32(buf, TAG_Index, &point));
      Bit *bit = Bit::Read(buf);
      Try(ReadCloseTag(buf, TAG_SummaryAssert));

      res->AddAssert((AssertKind)kind, (AssertClass)cls, point, bit);
      break;
    }

    case TAG_SummaryAssume: {
      Try(res);

      Try(ReadOpenTag(buf, TAG_SummaryAssume));
      Bit *bit = Bit::Read(buf);
      Try(ReadCloseTag(buf, TAG_SummaryAssume));

      res->AddAssume(bit);
      break;
    }

    default:
      Try(false);
    }
  }

  Try(res);
  return res;
}

void BlockSummary::WriteList(Buffer *buf, const Vector<BlockSummary*> &sums)
{
  Assert(buf->pos == buf->base);
  for (size_t ind = 0; ind < sums.Size(); ind++)
    Write(buf, sums[ind]);
}

void BlockSummary::ReadList(Buffer *buf, Vector<BlockSummary*> *sums)
{
  Assert(buf->pos == buf->base);

  while (buf->pos != buf->base + buf->size) {
    BlockSummary *sum;
    Try(sum = Read(buf));
    sums->PushBack(sum);
  }
}

// visitor to add assumptions for any global or type invariants relevant
// to an lvalue accessed within a function.
struct InvariantAssumeVisitor : public ExpVisitor
{
public:
  BlockMemory *mcfg;
  PPoint point;
  Vector<AssumeInfo> *assume_list;

  InvariantAssumeVisitor(BlockMemory *_mcfg, PPoint _point,
                         Vector<AssumeInfo> *_assume_list)
    : ExpVisitor(VISK_LvalSubExprs), mcfg(_mcfg), point(_point),
      assume_list(_assume_list)
  {}

  void Visit(Exp *exp)
  {
    if (ExpFld *nexp = exp->IfFld()) {
      // pick up any type invariants from the host type.
      String *csu_name = nexp->GetField()->GetCSUType()->GetCSUName();
      Vector<BlockCFG*> *annot_list = CompAnnotCache.Lookup(csu_name);

      for (size_t ind = 0; annot_list && ind < annot_list->Size(); ind++) {
        BlockCFG *annot_cfg = annot_list->At(ind);
        Assert(annot_cfg->GetAnnotationKind() == AK_Invariant ||
               annot_cfg->GetAnnotationKind() == AK_InvariantAssume);
        BlockId *id = annot_cfg->GetId();

        Bit *bit = BlockMemory::GetAnnotationBit(annot_cfg);
        if (!bit) continue;

        // get the *this expression. we'll replace this with the actual CSU
        // lvalue to get the assumed bit.
        Variable *this_var = Variable::Make(id, VK_This, NULL, 0, NULL);
        Exp *this_exp = Exp::MakeVar(this_var);
        Exp *this_drf = Exp::MakeDrf(this_exp);
        Exp *target = nexp->GetTarget();

        GuardExpVector lval_res;
        if (mcfg)
          mcfg->TranslateExp(TRK_Point, point, target, &lval_res);
        else
          lval_res.PushBack(GuardExp(target, Bit::MakeConstant(true)));

        for (size_t lind = 0; lind < lval_res.Size(); lind++) {
          // ignore the guard component of the result here. this means that
          // accessing a field of a value means related invariants hold for
          // the value along all paths. which is normally right, except when
          // the value is the result of a cast, and could have a different type
          // along other paths. TODO: sort this out.
          const GuardExp &gs = lval_res[lind];
          Bit *new_bit = BitReplaceExp(bit, this_drf, gs.exp);

          AssumeInfo info;
          info.annot = annot_cfg;
          info.point = 0;
          info.bit = new_bit;
          assume_list->PushBack(info);
        }
      }

      CompAnnotCache.Release(csu_name);
    }

    if (ExpVar *nexp = exp->IfVar()) {
      if (nexp->GetVariable()->Kind() == VK_Glob) {
        String *var_name = nexp->GetVariable()->GetName();
        Vector<BlockCFG*> *annot_list = InitAnnotCache.Lookup(var_name);

        for (size_t ind = 0; annot_list && ind < annot_list->Size(); ind++) {
          BlockCFG *annot_cfg = annot_list->At(ind);
          Assert(annot_cfg->GetAnnotationKind() == AK_Invariant ||
                 annot_cfg->GetAnnotationKind() == AK_InvariantAssume);

          Bit *bit = BlockMemory::GetAnnotationBit(annot_cfg);
          if (!bit) continue;

          AssumeInfo info;
          info.annot = annot_cfg;
          info.point = 0;
          info.bit = bit;
          assume_list->PushBack(info);
        }

        InitAnnotCache.Release(var_name);
      }
    }
  }
};

// get the caller bit to assume given a callee assumption.
static Bit* GetCallerAssume(BlockMemory *mcfg, PEdge *edge,
                            BlockId *callee, bool indirect, Bit *bit)
{
  PPoint call_point = edge->GetSource();

  // watch out for the case when the callee refers to data that has no caller
  // representation, such as missing arguments but particularly missing return
  // values. in this case translating the callee bit will produce 'false',
  // which is not what we want.
  if (!mcfg->CanTranslateCalleeBit(call_point, bit))
    return NULL;

  Bit *caller_bit;
  mcfg->TranslateBit(TRK_CalleeExit, call_point, bit, &caller_bit);

  if (indirect) {
    // transform the assumed bit into '(receiver != callee) || bit'.
    // when split out across the possible receivers, this goes to:
    // bit || (g0 && r0 != callee) || (g1 && r1 != callee) || ...

    Variable *callee_var = callee->BaseVar();
    Exp *callee_exp = Exp::MakeVar(callee_var);

    GuardExpVector receiver_list;
    mcfg->TranslateReceiver(call_point, &receiver_list);

    for (size_t ind = 0; ind < receiver_list.Size(); ind++) {
      const GuardExp &gs = receiver_list[ind];
      Bit *ne_bit = Exp::MakeCompareBit(B_NotEqual, callee_exp, gs.exp);
      ne_bit = Bit::MakeAnd(ne_bit, gs.guard);

      caller_bit = Bit::MakeOr(caller_bit, ne_bit);
    }
  }

  return caller_bit;
}

// get any assumptions from a call/loop to callee through edge.
static void GetCallAssumedBits(BlockMemory *mcfg, PEdge *edge,
                               BlockId *callee, bool indirect,
                               Vector<AssumeInfo> *assume_list)
{
  // add inferred assumptions from the callee.

  BlockSummary *sum = GetBlockSummary(callee);

  const Vector<Bit*> *assumes = sum->GetAssumes();
  size_t assume_count = VectorSize<Bit*>(assumes);

  for (size_t ind = 0; ind < assume_count; ind++) {
    Bit *bit = assumes->At(ind);
    Bit *caller_bit = GetCallerAssume(mcfg, edge, callee, indirect, bit);

    if (!caller_bit) continue;

    AssumeInfo info;
    info.point = edge->GetSource();
    info.bit = caller_bit;
    assume_list->PushBack(info);
  }

  // add annotated postconditions from the callee.

  // only do this for call edges.
  if (!edge->IsCall())
    return;

  Vector<BlockCFG*> *annot_list = BodyAnnotCache.Lookup(callee->Function());

  for (size_t ind = 0; annot_list && ind < annot_list->Size(); ind++) {
    BlockCFG *annot_cfg = annot_list->At(ind);

    if (annot_cfg->GetAnnotationKind() != AK_Postcondition &&
        annot_cfg->GetAnnotationKind() != AK_PostconditionAssume)
      continue;

    Bit *bit = BlockMemory::GetAnnotationBit(annot_cfg);
    if (!bit) continue;

    Bit *caller_bit = GetCallerAssume(mcfg, edge, callee, indirect, bit);
    if (!caller_bit) continue;

    AssumeInfo info;
    info.annot = annot_cfg;
    info.point = edge->GetSource();
    info.bit = caller_bit;
    assume_list->PushBack(info);
  }

  BodyAnnotCache.Release(callee->Function());
}

void BlockSummary::GetAssumedBits(BlockMemory *mcfg, PPoint end_point,
                                  Vector<AssumeInfo> *assume_list)
{
  BlockId *id = mcfg->GetId();
  BlockCFG *cfg = mcfg->GetCFG();

  BlockSummary *sum = GetBlockSummary(id);

  const Vector<Bit*> *assumes = sum->GetAssumes();
  size_t assume_count = VectorSize<Bit*>(assumes);

  // pull in assumptions from the summary for mcfg. in some cases these
  // assumptions won't be useful, e.g. describing the state at exit
  // for functions. for now we're just adding all of them though. TODO: fix.
  for (size_t ind = 0; ind < assume_count; ind++) {
    Bit *bit = assumes->At(ind);

    AssumeInfo info;
    info.bit = bit;
    assume_list->PushBack(info);
  }

  Vector<BlockCFG*> *annot_list = BodyAnnotCache.Lookup(id->Function());

  // add assumes at function entry for any preconditions.

  if (id->Kind() == B_Function) {
    for (size_t ind = 0; annot_list && ind < annot_list->Size(); ind++) {
      BlockCFG *annot_cfg = annot_list->At(ind);

      if (annot_cfg->GetAnnotationKind() != AK_Precondition &&
          annot_cfg->GetAnnotationKind() != AK_PreconditionAssume)
        continue;

      Bit *bit = BlockMemory::GetAnnotationBit(annot_cfg);
      if (!bit) continue;

      AssumeInfo info;
      info.annot = annot_cfg;
      info.bit = bit;
      assume_list->PushBack(info);
    }
  }

  // add assumptions from points within the block.

  for (size_t pind = 0; pind < cfg->GetPointAnnotationCount(); pind++) {
    PointAnnotation pann = cfg->GetPointAnnotation(pind);
    if (end_point && pann.point >= end_point)
      continue;

    BlockCFG *annot_cfg = GetAnnotationCFG(pann.annot);
    if (!annot_cfg) continue;

    Assert(annot_cfg->GetAnnotationKind() != AK_AssertRuntime);

    if (Bit *bit = BlockMemory::GetAnnotationBit(annot_cfg)) {
      // get the annotation bit in terms of block entry.
      Bit *point_bit = NULL;
      mcfg->TranslateBit(TRK_Point, pann.point, bit, &point_bit);

      AssumeInfo info;
      info.annot = annot_cfg;
      info.point = pann.point;
      info.bit = point_bit;
      assume_list->PushBack(info);
    }
  }

  // add assumptions from annotation edges within the block, invariants
  // on values accessed by the block, and from the summaries of any callees.

  for (size_t eind = 0; eind < cfg->GetEdgeCount(); eind++) {
    PEdge *edge = cfg->GetEdge(eind);
    PPoint point = edge->GetSource();

    if (end_point && point >= end_point)
      continue;

    InvariantAssumeVisitor visitor(mcfg, point, assume_list);
    edge->DoVisit(&visitor);

    if (PEdgeAnnotation *nedge = edge->IfAnnotation()) {
      // add an assumption for this annotation.
      BlockCFG *annot_cfg = GetAnnotationCFG(nedge->GetAnnotationId());
      if (!annot_cfg) continue;

      Bit *bit = BlockMemory::GetAnnotationBit(annot_cfg);

      // don't incorporate AssertRuntimes, these are not assumed.
      if (bit && annot_cfg->GetAnnotationKind() != AK_AssertRuntime) {
        // get the annotation bit in terms of block entry.
        Bit *point_bit = NULL;
        mcfg->TranslateBit(TRK_Point, point, bit, &point_bit);

        AssumeInfo info;
        info.annot = annot_cfg;
        info.point = point;
        info.bit = point_bit;
        assume_list->PushBack(info);
      }
    }

    if (BlockId *callee = edge->GetDirectCallee()) {
      GetCallAssumedBits(mcfg, edge, callee, false, assume_list);
    }
    else if (edge->IsCall()) {
      // add conditional assumes for the indirect targets of the call.
      // this is most useful for baked information and annotations, where
      // we sometimes need to attach information at indirect calls.

      CallEdgeSet *callees = CalleeCache.Lookup(id->BaseVar());
      size_t old_count = assume_list->Size();

      if (callees) {
        for (size_t cind = 0; cind < callees->GetEdgeCount(); cind++) {
          const CallEdge &cedge = callees->GetEdge(cind);
          if (cedge.where.id == id && cedge.where.point == point) {
            BlockId *callee = BlockId::Make(B_Function, cedge.callee);
            GetCallAssumedBits(mcfg, edge, callee, true, assume_list);
          }
        }
      }

      if (assume_list->Size() != old_count) {
        // we managed to do something at this indirect call site.
        // add another assumption restricting the possible callees to
        // only those identified by our callgraph.

        GuardExpVector receiver_list;
        mcfg->TranslateReceiver(point, &receiver_list);

        for (size_t rind = 0; rind < receiver_list.Size(); rind++) {
          const GuardExp &gs = receiver_list[rind];

          // make a bit: !when || rcv == callee0 || rcv == callee1 || ...
          Bit *extra_bit = Bit::MakeNot(gs.guard);

          for (size_t cind = 0; cind < callees->GetEdgeCount(); cind++) {
            const CallEdge &cedge = callees->GetEdge(cind);
            if (cedge.where.id == id && cedge.where.point == point) {
              Variable *callee_var = cedge.callee;
              Exp *callee_exp = Exp::MakeVar(callee_var);
              Bit *equal = Exp::MakeCompareBit(B_Equal, callee_exp, gs.exp);
              extra_bit = Bit::MakeOr(extra_bit, equal);
            }
          }

          AssumeInfo info;
          info.bit = extra_bit;
          assume_list->PushBack(info);
        }
      }

      CalleeCache.Release(id->BaseVar());
    }
  }

  BodyAnnotCache.Release(id->Function());

  // add assumptions from heap invariants describing values mentioned
  // in added assumptions. we could keep doing this transitively but don't,
  // to ensure termination.
  size_t count = assume_list->Size();
  for (size_t ind = 0; ind < count; ind++) {
    InvariantAssumeVisitor visitor(NULL, 0, assume_list);
    assume_list->At(ind).bit->DoVisit(&visitor);
  }

  CombineAssumeList(assume_list);
}

bool BlockSummary::GetAssertFunction(const char *name, Buffer *buf)
{
  // remove everything before the first two '$' signs (kind and filename).
  const char *pos = strchr(name, '$');
  if (!pos) return false;
  pos = strchr(pos + 1, '$');
  if (!pos) return false;
  pos++;

  // the function name is everything up to the next '$', excluding the
  // loop name (if there is one) and assert index.
  const char *next_pos = strchr(pos, '$');
  if (!next_pos) return false;

  buf->Append(pos, next_pos - pos);
  buf->Ensure(1);
  *buf->pos = 0;

  return true;
}

struct GCSafeFieldVisitor : public ExpVisitor
{
  Field *field;
  bool safe;

  GCSafeFieldVisitor(Field *field)
    : ExpVisitor(VISK_All), field(field), safe(false)
  {}

  void Visit(Exp *exp)
  {
    if (ExpGCSafe *nexp = exp->IfGCSafe()) {
      Exp *target = nexp->GetLvalTarget();
      if (ExpFld *ntarget = target->IfFld()) {
        // hack around broken fields in annotations. FIXME
        Field *new_field = ntarget->GetField();
        if (new_field->GetCSUType() == field->GetCSUType() &&
            new_field->GetSourceName() == field->GetSourceName()) {
          safe = true;
        }
      }
    }
  }
};

bool BlockSummary::FieldIsGCSafe(Field *field)
{
  String *csu_name = field->GetCSUType()->GetCSUName();
  Vector<BlockCFG*> *annot_list = CompAnnotCache.Lookup(csu_name);

  for (size_t ind = 0; annot_list && ind < annot_list->Size(); ind++) {
    BlockCFG *annot_cfg = annot_list->At(ind);
    Assert(annot_cfg->GetAnnotationKind() == AK_Invariant ||
           annot_cfg->GetAnnotationKind() == AK_InvariantAssume);

    Bit *bit = BlockMemory::GetAnnotationBit(annot_cfg);
    if (!bit) continue;

    GCSafeFieldVisitor visitor(field);
    bit->DoVisit(&visitor);

    if (visitor.safe)
      return true;
  }

  return false;
}

/////////////////////////////////////////////////////////////////////
// BlockSummary
/////////////////////////////////////////////////////////////////////

BlockSummary::BlockSummary(BlockId *id)
  : m_id(id), m_mcfg(NULL), m_assert_list(NULL), m_assume_list(NULL)
{
  Assert(m_id);
  m_hash = m_id->Hash();
}

void BlockSummary::SetMemory(BlockMemory *mcfg)
{
  Assert(mcfg->GetId() == GetId());

  if (m_mcfg == NULL)
    m_mcfg = mcfg;
}

void BlockSummary::AddAssert(AssertKind kind, AssertClass cls,
                             PPoint point, Bit *bit)
{
  if (m_assert_list == NULL)
    m_assert_list = new Vector<AssertInfo>();

  // maintain the list of assertions in order, sorted by kind,
  // then class, then point, then bit.
  size_t insert_index = 0;

  for (; insert_index < m_assert_list->Size(); insert_index++) {
    const AssertInfo &info = m_assert_list->At(insert_index);

    if (info.kind == kind && info.cls == cls &&
        info.point == point && info.bit == bit) {
      // found a duplicate assertion.
      return;
    }

    if (kind < info.kind)
      break;
    else if (kind == info.kind) {
      if (cls < info.cls)
        break;
      else if (cls == info.cls) {
        if (point < info.point)
          break;
        else if (point == info.point) {
          if (bit < info.bit)
            break;
        }
      }
    }
  }

  // add an entry at the end and shift all entries after the insert point.
  m_assert_list->PushBack(AssertInfo());
  for (size_t ind = m_assert_list->Size() - 1; ind > insert_index; ind--)
    m_assert_list->At(ind) = m_assert_list->At(ind - 1);

  AssertInfo &info = m_assert_list->At(insert_index);
  info.kind = kind;
  info.cls = cls;
  info.point = point;
  info.bit = bit;
}

void BlockSummary::AddAssume(Bit *bit)
{
  if (m_assume_list == NULL)
    m_assume_list = new Vector<Bit*>();

  if (!m_assume_list->Contains(bit))
    m_assume_list->PushBack(bit);
}

void BlockSummary::ComputeAssertNames()
{
  BlockCFG *cfg = GetBlockCFG(m_id);
  Assert(cfg);

  // the assertion names need the filename of the containing function.
  Location *loc = cfg->GetPointLocation(cfg->GetEntryPoint());

  // keep track of the last kind/index to be generated for an assertion.
  // the index space should be different for each assertion kind so that
  // different assertions do not interfere with one another. we can get this
  // with a simple counter because the assertions are sorted by kind.
  AssertKind last_kind = ASK_None;
  size_t last_index = 0;

  for (size_t ind = 0; m_assert_list && ind < m_assert_list->Size(); ind++) {
    AssertInfo &info = m_assert_list->At(ind);
    Assert(!info.name_buf);

    // only compute indexes for assertions which need to be checked.
    if (info.cls != ASC_Check) continue;

    // reset the index if this is a new kind of assertion.
    if (info.kind != last_kind) {
      last_kind = info.kind;
      last_index = 0;
    }
    last_index++;

    info.name_buf = new Buffer(256);
    BufferOutStream out(info.name_buf);

    out << AssertKindString(last_kind) << "$"
        << loc->FileName()->Value() << "$"
        << m_id->Function()->Value() << "$"
        << (m_id->Kind() == B_Loop ? m_id->Loop()->Value() : "func") << "$"
        << last_index << '\0';
  }
}

void BlockSummary::Print(OutStream &out) const
{
  out << "summary: " << m_id << endl;

  size_t assert_count = VectorSize<AssertInfo>(m_assert_list);
  for (size_t ind = 0; ind < assert_count; ind++) {
    const AssertInfo &info = m_assert_list->At(ind);
    out << "  assert " << AssertKindString(info.kind)
        << " " << AssertClassString(info.cls)
        << ": " << info.point << ": " << info.bit << endl;
  }

  size_t assume_count = VectorSize<Bit*>(m_assume_list);
  for (size_t ind = 0; ind < assume_count; ind++)
    out << "  assume: " << m_assume_list->At(ind) << endl;
}

void BlockSummary::MarkChildren() const
{
  m_id->Mark();

  if (m_mcfg)
    m_mcfg->Mark();

  if (m_assert_list) {
    for (size_t ind = 0; ind < m_assert_list->Size(); ind++)
      m_assert_list->At(ind).bit->Mark();
  }

  if (m_assume_list) {
    for (size_t ind = 0; ind < m_assume_list->Size(); ind++)
      m_assume_list->At(ind)->Mark();
  }
}

void BlockSummary::Persist()
{}

void BlockSummary::UnPersist()
{ 
  m_mcfg = NULL;

  if (m_assert_list) {
    delete m_assert_list;
    m_assert_list = NULL;
  }

  if (m_assume_list) {
    delete m_assume_list;
    m_assume_list = NULL;
  }
}

NAMESPACE_XGILL_END
