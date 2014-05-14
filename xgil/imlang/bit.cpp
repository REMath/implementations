
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

#include "bit.h"

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// Bit static
/////////////////////////////////////////////////////////////////////

HashCons<Bit> Bit::g_table;

bool Bit::g_extra_used = false;
bool Bit::g_replace_used = false;
bool Bit::g_base_used = false;

int Bit::Compare(const Bit *b0, const Bit *b1)
{
  TryCompareValues(b0->Kind(), b1->Kind());

  switch (b0->Kind()) {
  case BIT_Var:
    TryCompareObjects(b0->GetVar(), b1->GetVar(), Exp);
    break;
  default:
    TryCompareValues(b0->GetOperandCount(), b1->GetOperandCount());
    for (size_t ind = 0; ind < b0->GetOperandCount(); ind++) {
      Bit *op0 = b0->GetOperand(ind);
      Bit *op1 = b1->GetOperand(ind);
      TryCompareObjects(op0, op1, Bit);
    }
    break;
  }

  return 0;
}

Bit* Bit::Copy(const Bit *b)
{
  return new Bit(*b);
}

void Bit::Write(Buffer *buf, Bit *b)
{
  WriteOpenTag(buf, TAG_Bit);
  uint32_t id = 0;
  if (buf->TestSeen((uint64_t)b, &id)) {
    WriteUInt32(buf, id);
  }
  else {
    WriteUInt32(buf, id);

#ifdef SERIAL_CHECK_HASHES
    WriteTagUInt32(buf, TAG_Hash, b->Hash());
#endif

    // haven't written this bit before, write out its contents.
    WriteTagUInt32(buf, TAG_Kind, b->Kind());
    switch (b->Kind()) {
    case BIT_False:
    case BIT_True:
      break;
    case BIT_Var:
      Exp::Write(buf, b->GetVar());
      break;
    case BIT_And:
    case BIT_Not:
    case BIT_Or:
      for (size_t oind = 0; oind < b->GetOperandCount(); oind++)
        Write(buf, b->GetOperand(oind));
      break;
    default:
      Assert(false);
    }
  }
  WriteCloseTag(buf, TAG_Bit);
}

Bit* Bit::Read(Buffer *buf)
{
  uint32_t id = 0;
  uint32_t kind = 0;
  Exp *var = NULL;
  Vector<Bit*> op_list;

  Try(ReadOpenTag(buf, TAG_Bit));
  Try(ReadUInt32(buf, &id));

  uint64_t v = 0;
  if (buf->TestSeenRev((size_t)id, &v)) {
    Try(ReadCloseTag(buf, TAG_Bit));
    return (Bit*) v;
  }

  uint32_t hash = 0;

  while (!ReadCloseTag(buf, TAG_Bit)) {
    switch (PeekOpenTag(buf)) {
    case TAG_Kind: {
      Try(!kind);
      Try(ReadTagUInt32(buf, TAG_Kind, &kind));
      break;
    }
    case TAG_Bit: {
      Bit *bit = Read(buf);
      op_list.PushBack(bit);
      break;
    }
    case TAG_Exp: {
      Try(!var);
      var = Exp::Read(buf);
      break;
    }
    case TAG_Hash: {
      Try(ReadTagUInt32(buf, TAG_Hash, &hash));
      break;
    }
    default:
      Try(false);
    }
  }

  // this is only needed if the expression simplification rules
  // are different between serialization and deserialization.
  SortBitList(&op_list);

  Bit *bit = NULL;
  switch ((BitKind) kind) {
  case BIT_True:
    bit = MakeConstant(true);
    break;
  case BIT_False:
    bit = MakeConstant(false);
    break;
  case BIT_Var:
    Try(var != NULL);
    bit = MakeVar(var);
    break;
  case BIT_Not:
    Try(op_list.Size() == 1);
    bit = MakeNot(op_list[0], BSIMP_None);
    break;
  case BIT_And:
    bit = MakeAnd(op_list, BSIMP_None);
    break;
  case BIT_Or:
    bit = MakeOr(op_list, BSIMP_None);
    break;
  default:
    Try(false);
  }

  Assert(bit != NULL);

#ifdef SERIAL_CHECK_HASHES
  if (hash)
    Assert(bit->Hash() == hash);
#endif

  if (!buf->AddSeenRev(id, (uint64_t) bit)) {
    // the references on var/op_list have already been consumed
    return NULL;
  }
  return bit;
}

Bit* Bit::MakeConstant(bool constant)
{
  Bit bit(constant);
  return g_table.Lookup(bit);
}

Bit* Bit::MakeVar(Exp *var)
{
  Bit bit(var);
  return g_table.Lookup(bit);
}

Bit* Bit::MakeNot(Bit *op, BitSimplifyLevel level)
{
  // short circuit the !(!(B)) case
  if (op->Kind() == BIT_Not)
    return op->GetOperand(0);

  Vector<Bit*> data;
  data.PushBack(op);

  Bit bit(BIT_Not, data);
  return SimplifyBit(bit, level);
}

Bit* Bit::MakeAnd(Bit *op0, Bit *op1, BitSimplifyLevel level)
{
  // short circuit the (B & B), (B & false) and (B & true) cases
  if (op0 == op1 || op0->IsTrue() || op1->IsFalse())
    return op1;
  if (op1->IsTrue() || op0->IsFalse())
    return op0;

  Vector<Bit*> data;
  if (CompareObjects<Bit>(op0, op1) < 0) {
    data.PushBack(op0);
    data.PushBack(op1);
  }
  else {
    data.PushBack(op1);
    data.PushBack(op0);
  }

  Bit bit(BIT_And, data);
  return SimplifyBit(bit, level);
}

Bit* Bit::MakeAnd(const Vector<Bit*> &op_list, BitSimplifyLevel level)
{
  Bit bit(BIT_And, op_list);
  return SimplifyBit(bit, level);
}

Bit* Bit::MakeOr(Bit *op0, Bit *op1, BitSimplifyLevel level)
{
  // short circuit the (B | B), (B | false) and (B | true) cases
  if (op0 == op1 || op0->IsFalse() || op1->IsTrue())
    return op1;
  if (op1->IsFalse() || op0->IsTrue())
    return op0;

  Vector<Bit*> data;
  if (CompareObjects<Bit>(op0, op1) < 0) {
    data.PushBack(op0);
    data.PushBack(op1);
  }
  else {
    data.PushBack(op1);
    data.PushBack(op0);
  }

  Bit bit(BIT_Or, data);
  return SimplifyBit(bit, level);
}

Bit* Bit::MakeOr(const Vector<Bit*> &op_list, BitSimplifyLevel level)
{
  Bit bit(BIT_Or, op_list);
  return SimplifyBit(bit, level);
}

Bit* Bit::MakeImply(Bit *op0, Bit *op1, BitSimplifyLevel level)
{
  Bit *nop0 = MakeNot(op0, level);
  return MakeOr(nop0, op1, level);
}

Bit* Bit::ReduceBit(Bit *bit, Bit *base)
{
  Bit *res = NULL;

  switch (base->Kind()) {
  case BIT_False: {
    // result is false.
    res = base;
    break;
  }
  case BIT_True: {
    // result is unchanged.
    res = bit;
    break;
  }
  case BIT_Var:
  case BIT_Not:
  case BIT_Or: {
    // replace sub-formulas of bit implied directly by base.
    Vector<Bit*> operands;
    operands.PushBack(base);

    Assert(!g_replace_used);
    g_replace_used = true;
    res = ReplaceImplied(bit, operands, operands.Size(), true,
                         REPLACE_IMPLIED_MAX_DEPTH);
    g_replace_used = false;

    bit->ClearReplaceExtra();
    break;
  }
  case BIT_And: {
    // replace sub-formulas of bit implied by any operand of base.
    Vector<Bit*> operands;
    for (size_t oind = 0; oind < base->GetOperandCount(); oind++)
      operands.PushBack(base->GetOperand(oind));

    Assert(!g_replace_used);
    g_replace_used = true;
    res = ReplaceImplied(bit, operands, operands.Size(), true,
                         REPLACE_IMPLIED_MAX_DEPTH);
    g_replace_used = false;

    bit->ClearReplaceExtra();
    break;
  }
  default:
    Assert(false);
  }

  if (g_callback_BitSimplify) {
    Bit *old_and = MakeAnd(bit, base, BSIMP_None);
    Bit *new_and = MakeAnd(res, base, BSIMP_None);
    g_callback_BitSimplify(old_and, new_and);
  }

  return res;
}

#define TRY_PRINT(where)                          \
  do {                                            \
    if (printing) {                               \
      logout << "  " << where << endl;            \
      nb->PrintTree(logout, 2);                   \
    }                                             \
  } while (0)

Bit* Bit::SimplifyBit(Bit &b, BitSimplifyLevel level)
{
  // maintain the invariant that we hold a single reference on nb.
  // each time nb changes, we get a reference on the new value,
  // then remove it on the old value
  Bit *nb = g_table.Lookup(b);

  // keep a second reference around for debugging and checking purposes.
  Bit *old_nb = nb;

  bool printing = false;

  if (printing)
    logout << "[[bitsimp]]" << endl;

  TRY_PRINT("initial");

  switch (level) {
  case BSIMP_None:
    break;
  case BSIMP_Fold:
    SimplifyConstantFold(&nb);
    TRY_PRINT("constantfold");
    SimplifyDegenerate(&nb);
    TRY_PRINT("degenerate");
    SimplifyDeMorgan(&nb);
    TRY_PRINT("demorgan");
    SimplifyFlatten(&nb);
    TRY_PRINT("flatten");
    break;
  case BSIMP_Full:
    SimplifyConstantFold(&nb);
    TRY_PRINT("constantfold");
    SimplifyDegenerate(&nb);
    TRY_PRINT("degenerate");
    SimplifyDeMorgan(&nb);
    TRY_PRINT("demorgan");
    SimplifyFlatten(&nb);
    TRY_PRINT("flatten");
    SimplifyRefactor(&nb);
    TRY_PRINT("refactored");
    SimplifyImplied(&nb);
    TRY_PRINT("implied");
    break;
  }

  if (g_callback_BitSimplify)
    g_callback_BitSimplify(old_nb, nb);

  // pass the reference on nb back up to the caller,
  // following the behavior of g_table.Lookup()
  return nb;
}

#undef TRY_PRINT
#undef SET_PRINT_BINOP

// replace the result *bit with nbit. this consumes a reference for nbit,
// and drops the held reference for *bit
static inline void ReplaceBit(Bit **bit, Bit *nbit)
{
  Assert(*bit != nbit);
  *bit = nbit;
}

void Bit::SimplifyConstantFold(Bit **pbit)
{
  // simplify not/and/or containing constant operands, and double negations

  Bit *obit = *pbit;
  switch (obit->Kind()) {
  case BIT_Not: {
    Bit *bbit = obit->GetOperand(0);
    switch (bbit->Kind()) {
    case BIT_True:
    case BIT_False: {
      Bit *nbit = MakeConstant(bbit->Kind() == BIT_False);
      ReplaceBit(pbit, nbit);
      return;
    }
    case BIT_Not: {
      Bit *nbit = bbit->GetOperand(0);
      ReplaceBit(pbit, nbit);
      return;
    }
    case BIT_Var: {
      // negate comparison vars.
      Exp *var = bbit->GetVar();
      if (ExpBinop *nvar = var->IfBinop()) {
        if (IsCompareBinop(nvar->GetBinopKind())) {
          BinopKind new_binop = NegateCompareBinop(nvar->GetBinopKind());
          Bit *nbit = Exp::MakeCompareBit(new_binop,
                              nvar->GetLeftOperand(), nvar->GetRightOperand(),
                              nvar->GetStrideType());
          ReplaceBit(pbit, nbit);
        }
      }
      return;
    }
    default:
      return;
    }
  }
  case BIT_And:
  case BIT_Or: {
    // hold a reference for each element of op_list
    Vector<Bit*> op_list;

    for (size_t oind = 0; oind < obit->GetOperandCount(); oind++) {
      Bit *mbit = obit->GetOperand(oind);
      switch (mbit->Kind()) {
      case BIT_True:
      case BIT_False: {
        // if this constant drives the result to true/false
        // then use that result.
        if ((obit->Kind() == BIT_And) == (mbit->Kind() == BIT_False)) {
          ReplaceBit(pbit, mbit);
          return;
        }
        // for other constants drop the op from the array
        break;
      }
      default:
        op_list.PushBack(mbit);
        break;
      }
    }

    Assert(op_list.Size() <= obit->GetOperandCount());
    if (op_list.Size() < obit->GetOperandCount()) {
      SortBitList(&op_list);
      Bit xbit(obit->Kind(), op_list);
      Bit *nbit = g_table.Lookup(xbit);

      ReplaceBit(pbit, nbit);
    }
    return;
  }
  default:
    return;
  }
}

void Bit::SimplifyDegenerate(Bit **pbit)
{
  // simplify degenerate binops containing zero or one operands

  Bit *obit = *pbit;
  if (obit->Kind() != BIT_And && obit->Kind() != BIT_Or)
    return;

  if (obit->GetOperandCount() == 0) {
    Bit *nbit = MakeConstant(obit->Kind() == BIT_And);
    ReplaceBit(pbit, nbit);
  }
  else if (obit->GetOperandCount() == 1) {
    Bit *nbit = obit->GetOperand(0);
    ReplaceBit(pbit, nbit);
  }
}

static inline BitKind ReverseBitBinop(BitKind kind)
{
  switch (kind) {
  case BIT_And:
    return BIT_Or;
  case BIT_Or:
    return BIT_And;
  default:
    Assert(false);
    return BIT_False;
  }
}

void Bit::SimplifyDeMorgan(Bit **pbit)
{
  // apply de morgan's rule to negated binops where the negated children
  // are at least as numerous as the non-negated children

  Bit *obit = *pbit;
  if (obit->Kind() != BIT_Not)
    return;

  Bit *negbit = obit->GetOperand(0);
  if (negbit->Kind() != BIT_And && negbit->Kind() != BIT_Or)
    return;

  size_t neg_count = 0;
  for (size_t oind = 0; oind < negbit->GetOperandCount(); oind++) {
    if (negbit->GetOperand(oind)->Kind() == BIT_Not)
      neg_count++;
  }

  if (neg_count >= negbit->GetOperandCount() - neg_count) {
    // hold a reference for each element of op_list
    Vector<Bit*> op_list;

    for (size_t oind = 0; oind < negbit->GetOperandCount(); oind++) {
      Bit *mbit = negbit->GetOperand(oind);
      op_list.PushBack(MakeNot(mbit, BSIMP_Fold));
    }

    BitKind kind = ReverseBitBinop(negbit->Kind());
    SortBitList(&op_list);
    Bit xbit(kind, op_list);
    Bit *nbit = g_table.Lookup(xbit);

    ReplaceBit(pbit, nbit);
  }
}

void Bit::SimplifyFlatten(Bit **pbit)
{
  // flatten binops with the same kind together.
  // apply de morgan's rule to any negated binops of the opposite kind

  Bit *obit = *pbit;
  if (obit->Kind() != BIT_And && obit->Kind() != BIT_Or)
    return;

  // hold a reference for each element of op_list
  Vector<Bit*> op_list;
  bool changed = false;

  for (size_t oind = 0; oind < obit->GetOperandCount(); oind++) {
    Bit *mbit = obit->GetOperand(oind);
    if (mbit->Kind() == obit->Kind()) {
      for (size_t mind = 0; mind < mbit->GetOperandCount(); mind++) {
        Bit *xmbit = mbit->GetOperand(mind);
        op_list.PushBack(xmbit);
      }
      changed = true;
      continue;
    }
    else if (mbit->Kind() == BIT_Not) {
      Bit *negbit = mbit->GetOperand(0);
      if (negbit->Kind() == ReverseBitBinop(obit->Kind())) {
        for (size_t nind = 0; nind < negbit->GetOperandCount(); nind++) {
          Bit *nmbit = negbit->GetOperand(nind);
          op_list.PushBack(MakeNot(nmbit, BSIMP_Fold));
        }
        changed = true;
        continue;
      }
    }

    // fall through
    op_list.PushBack(mbit);
  }

  if (changed) {
    SortBitList(&op_list);
    Bit xbit(obit->Kind(), op_list);
    Bit *nbit = g_table.Lookup(xbit);

    ReplaceBit(pbit, nbit);
  }
}

void Bit::SimplifyRefactor(Bit **pbit)
{
  // look for binops whose children all contain a common factor(s),
  // and bring that factor to the outer binop.
  // (X & Y) | (X & Z) == X & (Y | Z)

  Bit *obit = *pbit;
  if (obit->Kind() != BIT_And && obit->Kind() != BIT_Or)
    return;

  BitKind kind = obit->Kind();
  BitKind rev_kind = ReverseBitBinop(kind);

  // we should not see any degenerate binops here.
  Assert(obit->GetOperandCount() >= 2);

  // get a list of the bits shared between all operands of this binop.
  // these do not hold a reference.
  Vector<Bit*> common;

  // fill in common from the first operand
  Bit *op0 = obit->GetOperand(0);
  if (op0->Kind() == rev_kind) {
    for (size_t xoind = 0; xoind < op0->GetOperandCount(); xoind++)
      common.PushBack(op0->GetOperand(xoind));
  }
  else {
    common.PushBack(op0);
  }

  // prune from common all operands not in some child
  for (size_t oind = 1; oind < obit->GetOperandCount(); oind++) {
    Bit *op = obit->GetOperand(oind);

    for (size_t cind = 0; cind < common.Size(); ) {
      Bit *cop = common[cind];
      bool remove = true;

      if (op->Kind() == rev_kind) {
        for (size_t xoind = 0; xoind < op->GetOperandCount(); xoind++) {
          if (cop == op->GetOperand(xoind)) {
            remove = false;
            break;
          }
        }
      }
      else if (cop == op) {
        remove = false;
      }

      if (remove) {
        common[cind] = common.Back();
        common.PopBack();
      }
      else {
        cind++;
      }
    }

    if (common.Empty())
      break;
  }

  // factor out any common operands
  if (!common.Empty()) {

    // hold a reference for each element of op_list.
    // this holds the operands of the result.
    Vector<Bit*> op_list;

    // add the common bits to the result list of operands
    for (size_t cind = 0; cind < common.Size(); cind++) {
      Bit *cop = common[cind];
      op_list.PushBack(cop);
    }

    // hold a reference for each element of simp_op_list.
    // this holds the original operands with common factored out.
    Vector<Bit*> simp_op_list;

    // we can simplify down to the common operands if any operand of the
    // original bit is exactly equal to common, e.g.
    // A & (A | B) => A, A | (A & B) => A.
    bool drop_simp_list = false;

    // factor out common from each of the original operands
    for (size_t oind = 0; oind < obit->GetOperandCount(); oind++) {
      Bit *op = obit->GetOperand(oind);

      if (op->Kind() == rev_kind) {
        Vector<Bit*> fact_op_list;

        for (size_t xoind = 0; xoind < op->GetOperandCount(); xoind++) {
          Bit *xop = op->GetOperand(xoind);

          bool include = true;
          for (size_t cind = 0; cind < common.Size(); cind++) {
            if (xop == common[cind]) {
              include = false;
              break;
            }
          }

          if (include)
            fact_op_list.PushBack(xop);
        }

        if (fact_op_list.Empty()) {
          // empty result, the bit is exactly common
          Assert(common.Size() == op->GetOperandCount());
          drop_simp_list = true;
          break;
        }
        else if (fact_op_list.Size() == 1) {
          // result contains a single non-common bit from the operand.
          simp_op_list.PushBack(fact_op_list[0]);
        }
        else {
          // make a bit with the non-common parts of the operand.
          Bit fxbit(rev_kind, fact_op_list);
          Bit *fbit = g_table.Lookup(fxbit);
          simp_op_list.PushBack(fbit);
        }
      }
      else {
        // empty result, the bit is already in common.
        Assert(common.Size() == 1 && common[0] == op);
        drop_simp_list = true;
        break;
      }
    }

    if (!drop_simp_list) {
      Assert(simp_op_list.Size() == obit->GetOperandCount());

      // make a bit combining the simplified original operands.
      // do full simplification to hopefully remove some freshly
      // exposed implications and contradictions.
      SortBitList(&simp_op_list);
      Bit sxbit(kind, simp_op_list);
      Bit *sbit = SimplifyBit(sxbit, BSIMP_Full);

      op_list.PushBack(sbit);
    }

    // make a bit for the result.
    SortBitList(&op_list);
    Bit xbit(rev_kind, op_list);
    Bit *nbit = SimplifyBit(xbit, BSIMP_Fold);

    ReplaceBit(pbit, nbit);
  }
}

void Bit::SimplifyImplied(Bit **pbit)
{
  // check for operands of a binop which imply that a portion of
  // another operand is either true or false. the general idea is that
  // X & Y == X & Y[X -> true], and X | Y == X | Y[X -> false].

  // more generally, if the binop is X & Y & Z, any transitive sub-operand
  // of X can be replaced with true or false if its truthness is implied
  // by either Y or Z. likewise, any transitive sub-operand of Y can be
  // replaced by true or false as implied by Z and the *new* version of X,
  // and sub-operands of Z can be replaced according to the *new* versions
  // of X and Y. we need to use the new version so that, e.g. (a & a) is
  // simplified to (true & a), not (true & true).

  // disjunction is the same except that we replace sub-operands of X/Y/Z
  // whose truthness is implied by the negation of the other X/Y/Z values.

  Bit *obit = *pbit;
  if (obit->Kind() != BIT_And && obit->Kind() != BIT_Or)
    return;

  // hold a reference for each element of op_list.
  // this is initially a clone of the operands for the old bit,
  // and we will replace its members with the result of performing
  // implications as we proceed.
  Vector<Bit*> op_list;
  for (size_t iind = 0; iind < obit->GetOperandCount(); iind++) {
    Bit *ibit = obit->GetOperand(iind);
    op_list.PushBack(ibit);
  }

  // operands_true indicates whether we are assuming operands in the
  // outer binop other than the currently examined one are true or false.
  bool operands_true = (obit->Kind() == BIT_And);

  for (size_t oind = 0; oind < op_list.Size(); oind++) {
    Bit *ibit = op_list[oind];

    Assert(!g_replace_used);
    g_replace_used = true;
    Bit *nbit = ReplaceImplied(ibit, op_list, oind, operands_true,
                               REPLACE_IMPLIED_DEPTH);
    g_replace_used = false;

    ibit->ClearReplaceExtra();
    op_list[oind] = nbit;
  }

  // see if any bits in the list changed
  bool changed = false;
  for (size_t oind = 0; oind < op_list.Size(); oind++) {
    if (op_list[oind] != obit->GetOperand(oind)) {
      changed = true;
      break;
    }
  }

  if (changed) {
    SortBitList(&op_list);
    Bit xbit(obit->Kind(), op_list);
    Bit *nbit = SimplifyBit(xbit, BSIMP_Fold);

    ReplaceBit(pbit, nbit);

    // do the whole thing again. imply simplifications can cascade
    // and allow further imply simplifications to be performed.
    SimplifyImplied(pbit);
  }
}

Bit* Bit::ReplaceImplied(Bit *bit, const Vector<Bit*> &operands,
                         size_t cur_operand, bool operands_true,
                         size_t depth)
{
  // use the m_replace_extra field of a bit to store a Bit pointer
  // for the result of doing the replace with the specified arguments.
  // this field holds a reference on the replacement bit, which will be
  // dropped by ClearReplaceExtra.

  Assert(g_replace_used);

  if (bit->m_replace_extra != NULL) {
    // we already encountered and set this bit previously in the crawl.
    // return the previous value.
    return bit->m_replace_extra;
  }

  // is this bit directly implied as true or false by another operand?
  Bit *result = NULL;
  for (size_t oind = 0; oind < operands.Size(); oind++) {
    if (oind != cur_operand) {
      bool implied_result;
      bool implied = IsBitImplied(bit, operands[oind],
                                  operands_true, &implied_result);
      if (implied) {
        result = MakeConstant(implied_result);
        break;
      }
    }
  }

  if (result) {
    // nothing to do
  }
  else if (depth == 0) {
    // don't recurse, just use the bit as the result
    result = bit;
  }
  else {
    // recurse on any sub-operands, if any. keep track of whether
    // anything changed.
    Vector<Bit*> op_list;
    bool changed = false;
    for (size_t iind = 0; iind < bit->GetOperandCount(); iind++) {
      Bit *ibit = bit->GetOperand(iind);
      Bit *nibit = ReplaceImplied(ibit, operands, cur_operand,
                                  operands_true, depth - 1);
      if (ibit != nibit)
        changed = true;
      op_list.PushBack(nibit);
    }

    if (changed) {
      SortBitList(&op_list);
      Bit xbit(bit->Kind(), op_list);
      result = SimplifyBit(xbit, BSIMP_Fold);
    }
    else {
      result = bit;
    }
  }

  // store the result and consume the initial reference on it.
  bit->m_replace_extra = result;

  return result;
}

static inline bool IsBitNegation(Bit *bit, Bit *nbit)
{
  // handle simple negations here. this is not taking account of
  // more complex negations such as '(a & b) == !(!a | !b)',
  // which will be partially accounted for by the SimplifyImplied crawl.

  if (bit->Kind() == BIT_Not)
    return bit->GetOperand(0) == nbit;
  if (nbit->Kind() == BIT_Not)
    return bit == nbit->GetOperand(0);
  if (bit->Kind() == BIT_True)
    return nbit->Kind() == BIT_False;
  if (bit->Kind() == BIT_False)
    return nbit->Kind() == BIT_True;

  // dig into comparison negations a bit. a == b is the negation of a != b,
  // and a < b is the negation of b <= a. (due to the simplification rules
  // for expressions, these are the only possibilities we will see here).

  ExpBinop *var = bit->GetVar() ? bit->GetVar()->IfBinop() : NULL;
  ExpBinop *nvar = nbit->GetVar() ? nbit->GetVar()->IfBinop() : NULL;

  if (var && nvar) {
    BinopKind kind = NonPointerBinop(var->GetBinopKind());
    BinopKind nkind = NonPointerBinop(nvar->GetBinopKind());

    switch (kind) {
    case B_Equal:
    case B_NotEqual:
      if (nkind == (kind == B_Equal ? B_NotEqual : B_Equal)) {
        return (var->GetLeftOperand() == nvar->GetLeftOperand() &&
                var->GetRightOperand() == nvar->GetRightOperand());
      }
      break;
    case B_LessThan:
    case B_LessEqual:
      if (nkind == (kind == B_LessThan ? B_LessEqual : B_LessThan)) {
        return (var->GetLeftOperand() == nvar->GetRightOperand() &&
                var->GetRightOperand() == nvar->GetLeftOperand());
      }
      break;
    default:
      break;
    }
  }

  return false;
}

// compute if s implies that s_cmp is equal/notequal to s_val
static inline bool ComputeEquals(Exp *var, Exp **s_cmp,
                                 mpz_t s_val, bool *s_equal)
{
  if (ExpBinop *nvar = var->IfBinop()) {
    BinopKind kind = nvar->GetBinopKind();
    Exp *left_var = nvar->GetLeftOperand();
    Exp *right_var = nvar->GetRightOperand();

    if (kind == B_Equal || kind == B_NotEqual) {
      *s_equal = (kind == B_Equal);
      if (ExpInt *nleft = left_var->IfInt()) {
        nleft->GetMpzValue(s_val);
        *s_cmp = right_var;
        return true;
      }
      if (ExpInt *nright = right_var->IfInt()) {
        nright->GetMpzValue(s_val);
        *s_cmp = left_var;
        return true;
      }
    }
  }
  else {
    // value compared with is zero, which is the default for initialized mpz.
    *s_cmp = var;
    *s_equal = false;
    return true;
  }

  return false;
}

// when s/xs are variables in a boolean formula, get whether s is implied
// as true or false if xs is true or false. used by Bit::SimplifyImplied.
static inline bool IsVarImplied(Exp *s, Exp *xs,
                                bool xs_true, bool *s_true)
{
  // compute equality implication for xs
  Exp *xs_cmp;
  mpz_t xs_val;
  bool xs_equal;

  // compute equality implication for s
  Exp *s_cmp;
  mpz_t s_val;
  bool s_equal;

  mpz_init(xs_val);
  mpz_init(s_val);

  bool res = false;

  if (ComputeEquals(xs, &xs_cmp, xs_val, &xs_equal) &&
      ComputeEquals(s,  &s_cmp,  s_val,  &s_equal) &&
      xs_cmp == s_cmp) {
    if (!xs_true)
      xs_equal = !xs_equal;

    if (mpz_cmp(xs_val, s_val) == 0) {
      *s_true = (xs_equal == s_equal);
      res = true;
    }
    else if (xs_equal) {
      *s_true = !s_equal;
      res = true;
    }
  }

  mpz_clear(xs_val);
  mpz_clear(s_val);
  return res;
}

bool Bit::IsBitImplied(Bit *bit, Bit *xbit,
                       bool xbit_true, bool *bit_true)
{
  // get whether bit is implied as true or false if xbit is either
  // true or false. return true and set bit_true accordingly
  // if there is such an implication.

  // check if bit is trivially equal to xbit
  if (bit == xbit) {
    *bit_true = xbit_true;
    return true;
  }

  // check if bit is a simple negation of xbit
  if (IsBitNegation(bit, xbit)) {
    *bit_true = !xbit_true;
    return true;
  }

  // if bit and xbit are both variables or the negation of variables,
  // look for implications due to any underlying logic on those variables.

  Exp *bit_var = NULL;
  bool negate_bit_var = false;
  if (bit->Kind() == BIT_Var) {
    bit_var = bit->GetVar();
  }
  else if (bit->Kind() == BIT_Not) {
    if (bit->GetOperand(0)->Kind() == BIT_Var) {
      bit_var = bit->GetOperand(0)->GetVar();
      negate_bit_var = true;
    }
  }

  Exp *xbit_var = NULL;
  bool negate_xbit_var = false;
  if (xbit->Kind() == BIT_Var) {
    xbit_var = xbit->GetVar();
  }
  else if (xbit->Kind() == BIT_Not) {
    if (xbit->GetOperand(0)->Kind() == BIT_Var) {
      xbit_var = xbit->GetOperand(0)->GetVar();
      negate_xbit_var = true;
    }
  }

  if (bit_var && xbit_var) {
    bool xvar_true = negate_xbit_var ? !xbit_true : xbit_true;
    bool var_true;
    bool implied = IsVarImplied(bit_var, xbit_var, xvar_true, &var_true);

    if (implied) {
      *bit_true = negate_bit_var ? !var_true : var_true;
      return true;
    }
  }

  return false;
}

/////////////////////////////////////////////////////////////////////
// Bit
/////////////////////////////////////////////////////////////////////

Bit::Bit(bool constant)
  : m_kind(constant ? BIT_True : BIT_False),
    m_var(NULL), m_op_count(0), m_ops(NULL),
    m_extra(NULL), m_replace_extra(NULL), m_base_extra(false)
{
  m_hash = m_kind;
}

Bit::Bit(Exp *var)
  : m_kind(BIT_Var), m_var(var),
    m_op_count(0), m_ops(NULL),
    m_extra(NULL), m_replace_extra(NULL), m_base_extra(false)
{
  m_hash = Hash32(m_kind, m_var->Hash());
}

Bit::Bit(BitKind kind, const Vector<Bit*> &data)
  : m_kind(kind), m_var(NULL),
    m_op_count(data.Size()), m_ops(NULL),
    m_extra(NULL), m_replace_extra(NULL), m_base_extra(false)
{
  Assert(m_kind == BIT_And || m_kind == BIT_Or || m_kind == BIT_Not);
  if (m_kind == BIT_Not)
    Assert(m_op_count == 1);

  AssertArray(data.Data(), data.Size());
  Assert(IsSortedBitList(data));

  Bit **use_data;
  if (m_op_count <= BIT_BASE_CAPACITY) {
    for (size_t dind = 0; dind < m_op_count; dind++)
      m_base_ops[dind] = data[dind];
    use_data = (Bit**) &m_base_ops;
  }
  else {
    m_ops = (Bit**) data.Data();
    use_data = m_ops;
  }

  m_hash = m_kind;
  for (size_t ind = 0; ind < m_op_count; ind++)
    m_hash = Hash32(m_hash, use_data[ind]->Hash());
}

size_t Bit::Size()
{
  Assert(!g_base_used);
  g_base_used = true;
  size_t size = RecursiveSize();
  g_base_used = false;

  ClearBaseExtra();
  return size;
}

size_t Bit::RecursiveSize()
{
  Assert(g_base_used);

  // don't double count and/or bits encountered multiple times.
  if (m_base_extra) {
    if (m_kind == BIT_And || m_kind == BIT_Or)
      return 0;
  }

  m_base_extra = true;

  size_t size = 1;
  for (size_t oind = 0; oind < GetOperandCount(); oind++) {
    Bit *op = GetOperand(oind);
    size += op->RecursiveSize();
  }

  return size;
}

void Bit::PrintTree(OutStream &out, size_t pad_spaces)
{
  Assert(!g_base_used);
  g_base_used = true;
  RecursivePrintTree(out, pad_spaces);
  g_base_used = false;

  ClearBaseExtra();
}

void Bit::RecursivePrintTree(OutStream &out, size_t pad_spaces)
{
  Assert(g_base_used);
  PrintPadding(out, pad_spaces);

  // we will set the extra field to indicate that this has already been
  // printed out and just its hash should be used.
  if (m_base_extra) {
    // only print the hash for and/or binops.
    if (m_kind == BIT_And || m_kind == BIT_Or) {
      out << "# " << m_hash << endl;
      return;
    }
  }
  else {
    // set the extra field to indicate we visited and printed this node.
    m_base_extra = true;
  }

  switch (m_kind) {
  case BIT_False:
  case BIT_True:
  case BIT_Var:
    Print(out);
    out << endl;
    return;
  case BIT_Not:
    out << "NOT [" << m_hash << "]" << endl;
    break;
  case BIT_And:
    out << "AND [" << m_hash << "]" << endl;
    break;
  case BIT_Or:
    out << "OR [" << m_hash << "]" << endl;
    break;
  default:
    Assert(false);
  }

  for (size_t oind = 0; oind < GetOperandCount(); oind++) {
    Bit *op = GetOperand(oind);
    op->RecursivePrintTree(out, pad_spaces + 2);
  }
}

void Bit::DoVisit(ExpVisitor *visitor, bool revisit)
{
  if (!revisit) {
    Assert(!g_base_used);
    g_base_used = true;
  }

  RecursiveVisit(visitor, revisit);

  if (!revisit) {
    g_base_used = false;
    ClearBaseExtra();
  }
}

void Bit::RecursiveVisit(ExpVisitor *visitor, bool revisit)
{
  if (visitor->IsFinished())
    return;

  if (!revisit) {
    Assert(g_base_used);
    if (m_base_extra) {
      // we already visited this bit. don't revisit.
      return;
    }

    // make sure we only visit this once during the crawl.
    // TODO: the visitor might care about the phase of the bit. we need to
    // visit the bit twice in situations where it appears in both phases.
    m_base_extra = true;
  }

  switch (m_kind) {
  case BIT_True:
  case BIT_False:
    return;
  case BIT_Var:
    GetVar()->DoVisit(visitor);
    return;
  case BIT_Not:
    visitor->FlipPhase();
    GetOperand(0)->RecursiveVisit(visitor, revisit);
    visitor->FlipPhase();
    return;
  case BIT_Or:
    if (visitor->IgnoreDisjunction())
      return;
    // fall through.
  case BIT_And:
    for (size_t oind = 0; oind < GetOperandCount(); oind++)
      GetOperand(oind)->RecursiveVisit(visitor, revisit);
    break;
  default:
    Assert(false);
  }
}

Bit* Bit::DoMap(ExpMapper *mapper)
{
  // don't memoize bits encountered multiple times during mapping.
  // mapping should only be used for relatively compact bits.
  Bit *use_bit = NULL;

  switch (m_kind) {

  case BIT_True:
  case BIT_False:
    use_bit = this;
    break;

  case BIT_Var: {
    Exp *new_var = GetVar()->DoMap(mapper);
    if (new_var) {
      use_bit = Exp::MakeNonZeroBit(new_var);
    }
    else {
      switch (mapper->Widen()) {
      case WIDK_Drop:   use_bit = NULL; break;
      case WIDK_Widen:  use_bit = MakeConstant(true);  break;
      case WIDK_Narrow: use_bit = MakeConstant(false); break;
      }
    }
    break;
  }

  case BIT_Not: {
    mapper->FlipWiden();
    Bit *new_op = GetOperand(0)->DoMap(mapper);
    mapper->FlipWiden();

    if (new_op) {
      use_bit = MakeNot(new_op);
    }
    else {
      Assert(mapper->Widen() == WIDK_Drop);
      use_bit = NULL;
    }
    break;
  }

  case BIT_And:
  case BIT_Or: {
    Vector<Bit*> op_list;
    bool drop_op_list = false;

    for (size_t oind = 0; oind < GetOperandCount(); oind++) {
      Bit *new_op = GetOperand(oind)->DoMap(mapper);

      if (new_op) {
        op_list.PushBack(new_op);
      }
      else {
        Assert(mapper->Widen() == WIDK_Drop);
        drop_op_list = true;
        break;
      }
    }

    if (drop_op_list) {
      use_bit = NULL;
    }
    else {
      SortBitList(&op_list);

      if (m_kind == BIT_And) {
        use_bit = MakeAnd(op_list);
      }
      else {
        use_bit = MakeOr(op_list);
      }
    }
    break;
  }

  default:
    Assert(false);
  }

  return use_bit;
}

// helper for MultiMap. fill in res with all the possible permutations
// of mappings for ops[0..count-1].
void MultiMapBinop(bool is_and, Bit **ops, size_t count,
                   ExpMultiMapper *mapper, Vector<Bit*> *res)
{
  Assert(count > 0);

  if (count == 1) {
    ops[0]->DoMultiMap(mapper, res);
  }
  else {
    Vector<Bit*> prev_res;
    MultiMapBinop(is_and, ops, count - 1, mapper, &prev_res);

    for (size_t pind = 0; pind < prev_res.Size(); pind++) {
      Vector<Bit*> tail_res;
      ops[count-1]->DoMultiMap(mapper, &tail_res);

      for (size_t tind = 0; tind < tail_res.Size(); tind++) {
        Bit *new_bit;
        if (is_and)
          new_bit = Bit::MakeAnd(prev_res[pind], tail_res[tind]);
        else
          new_bit = Bit::MakeOr(prev_res[pind], tail_res[tind]);

        res->PushBack(new_bit);
      }
    }
  }
}

void Bit::DoMultiMap(ExpMultiMapper *mapper, Vector<Bit*> *res)
{
  // don't memoize bits encountered multiple times during multi-mapping.
  // multi-mapping should only be used for relatively compact bits.

  switch (m_kind) {

  case BIT_True:
  case BIT_False:
    res->PushBack(this);
    break;

  case BIT_Var: {
    Vector<Exp*> var_res;
    GetVar()->DoMultiMap(mapper, &var_res);

    for (size_t ind = 0; ind < var_res.Size(); ind++) {
      Bit *var_bit = Exp::MakeNonZeroBit(var_res[ind]);
      res->PushBack(var_bit);
    }

    break;
  }

  case BIT_Not: {
    Vector<Bit*> op_res;
    GetOperand(0)->DoMultiMap(mapper, &op_res);

    for (size_t ind = 0; ind < op_res.Size(); ind++) {
      Bit *not_bit = MakeNot(op_res[ind]);
      res->PushBack(not_bit);
    }

    break;
  }

  case BIT_And:
  case BIT_Or: {
    Bit **use_ops = m_ops ? m_ops : (Bit**) &m_base_ops;
    MultiMapBinop(m_kind == BIT_And, use_ops, m_op_count, mapper, res);
    break;
  }

  default:
    Assert(false);
  }
}

void Bit::Print(OutStream &out) const
{
  switch (m_kind) {
  case BIT_False:
    out << "false";
    break;
  case BIT_True:
    out << "true";
    break;
  case BIT_Var:
    out << GetVar();
    break;
  case BIT_Not:
    out << "!(" << GetOperand(0) << ")";
    break;
  case BIT_And:
  case BIT_Or: {
    out << "(";
    Bit **use_ops = m_ops ? m_ops : (Bit**) &m_base_ops;
    for (size_t ind = 0; ind < m_op_count; ind++) {
      if (ind != 0)
        out << (m_kind == BIT_And ? " && " : " || ");
      out << use_ops[ind];
    }
    out << ")";
    break;
  }
  default:
    Assert(false);
  }
}

void Bit::PrintUI(OutStream &out, bool parens) const
{
  switch (m_kind) {
  case BIT_False:
    out << "false";
    break;
  case BIT_True:
    out << "true";
    break;
  case BIT_Var:
    GetVar()->PrintUIRval(out, parens);
    break;
  case BIT_Not:
    out << "!";
    GetOperand(0)->PrintUI(out, true);
    break;
  case BIT_And:
  case BIT_Or: {
    if (parens)
      out << "(";
    Bit **use_ops = m_ops ? m_ops : (Bit**) &m_base_ops;
    for (size_t ind = 0; ind < m_op_count; ind++) {
      if (ind != 0)
        out << (m_kind == BIT_And ? " && " : " || ");
      use_ops[ind]->PrintUI(out, true);
    }
    if (parens)
      out << ")";
    break;
  }
  default:
    Assert(false);
  }
}

void Bit::MarkChildren() const
{
  if (m_var)
    m_var->Mark();
  Bit **use_ops = m_ops ? m_ops : (Bit**) &m_base_ops;
  for (size_t ind = 0; ind < m_op_count; ind++)
    use_ops[ind]->Mark();
}

void Bit::Persist()
{
  if (m_ops != NULL) {
    Bit **new_ops = new Bit*[m_op_count];
    memcpy(new_ops, m_ops, m_op_count * sizeof(Bit*));
    m_ops = new_ops;
  }
}

void Bit::UnPersist()
{
  if (m_ops != NULL) {
    delete m_ops;
    m_ops = NULL;
  }
}

void Bit::ClearReplaceExtra()
{
  Assert(!g_replace_used);

  if (m_replace_extra == NULL) {
    // we already encountered and cleared this bit previously in the crawl,
    // or this bit went beyond the max depth of the crawl.
    return;
  }

  m_replace_extra = NULL;

  // recurse on any sub-operands.
  for (size_t oind = 0; oind < GetOperandCount(); oind++) {
    Bit *obit = GetOperand(oind);
    obit->ClearReplaceExtra();
  }
}

void Bit::ClearBaseExtra()
{
  Assert(!g_base_used);

  if (!m_base_extra)
    return;

  m_base_extra = false;

  for (size_t oind = 0; oind < GetOperandCount(); oind++) {
    Bit *op = GetOperand(oind);
    op->ClearBaseExtra();
  }
}

void Bit::ClearExtra()
{
  Assert(!g_extra_used);

  if (m_extra == NULL) {
    // leaf node or cleared previously in crawl.
    return;
  }

  m_extra = NULL;

  for (size_t oind = 0; oind < GetOperandCount(); oind++) {
    Bit *op = GetOperand(oind);
    op->ClearExtra();
  }
}

class DirectiveVisitor : public ExpVisitor
{
public:
  DirectiveKind directive_kind;
  bool has_any_directive;
  bool has_target_directive;

  DirectiveVisitor(DirectiveKind kind)
    : ExpVisitor(VISK_All), directive_kind(kind),
      has_any_directive(false), has_target_directive(false)
  {}

  void Visit(Exp *exp)
  {
    if (ExpDirective *nexp = exp->IfDirective()) {
      has_any_directive = true;
      if (nexp->GetDirectiveKind() == directive_kind)
        has_target_directive = true;
    }
  }
};

bool BitHasDirective(Bit *bit, DirectiveKind kind)
{
  DirectiveVisitor visitor(kind);
  bit->DoVisit(&visitor, true);
  return visitor.has_target_directive;
}

bool BitHasAnyDirective(Bit *bit)
{
  DirectiveVisitor visitor((DirectiveKind)0);
  bit->DoVisit(&visitor, true);
  return visitor.has_any_directive;
}

NAMESPACE_XGILL_END
