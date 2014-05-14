
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

#include "constraint.h"
#include "solver.h"
#include <imlang/storage.h>
#include <memory/mstorage.h>

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// ConstraintTable
/////////////////////////////////////////////////////////////////////

TrackAlloc g_alloc_ConstraintTable("ConstraintTable");

ConstraintTable::ConstraintTable(const char *name, Solver *solver,
                                 size_t min_bucket_count)
  : m_alloc(g_alloc_ConstraintTable), m_name(name), m_solver(solver),
    m_buckets(NULL), m_bucket_count(0),
    m_entry_count(0), m_min_bucket_count(min_bucket_count)
{
  // as with solver hashtables, don't allocate until the first lookup.
  Assert(m_min_bucket_count);
  solver->AddConstraintTable(this);

  // push a context to receive any initial changes to undo with Clear().
  PushContext();
}

ConstraintTable::~ConstraintTable()
{
  Clear();

  // pop the remaining context and free its storage.
  PopContext();
}

void ConstraintTable::RegisterListener(ConstraintListenerFn function)
{
  Assert(m_entry_count == 0);
  Assert(!m_listener_functions.Contains(function));

  m_listener_functions.PushBack(function);
}

bool ConstraintTable::Insert(FrameId source_frame, Exp *source_exp,
                             FrameId target_frame, Exp *target_exp)
{
  if (m_bucket_count == 0)
    Resize(m_min_bucket_count);
  else
    CheckBucketCount();

  // look for a matching entry.

  uint32_t entry_hash = GetEntryHash(source_frame, source_exp,
                                     target_frame, target_exp);
  Bucket *entry_bucket = &m_buckets[entry_hash % m_bucket_count];

  ConstraintEntry *entry = entry_bucket->entry_begin;
  while (entry) {
    if (entry->frame == target_frame && entry->exp == target_exp &&
        entry->key->frame == source_frame && entry->key->exp == source_exp) {
      // already have an association between these two. bail out.
      return false;
    }
    entry = entry->next;
  }

  // make an entry for the association.

  if (m_solver->Verbose() && solver_constraint.IsSpecified()) {
    logout << "CONSTRAINT: Inserting " << m_name << ": "
           << source_exp << " [" << source_frame << "] -> "
           << target_exp << " [" << target_frame << "]" << endl;
  }

  m_entry_count++;

  ConstraintEntry *new_entry = track_new_single<ConstraintEntry>(m_alloc);
  new_entry->frame = target_frame;
  new_entry->exp = target_exp;

  LinkedListInsert<ConstraintEntry,__ConstraintEntry_List>
    (&entry_bucket->entry_pend, new_entry);

  // add the entry to the topmost context.
  TableContext *context = m_contexts.Back();
  context->entries.PushBack(new_entry);

  // connect the entry with its key.

  ConstraintKey *key = LookupKey(source_frame, source_exp, true);

  LinkedListInsert<ConstraintEntry,__ConstraintEntry_KeyList>
    (&key->entries_pend, new_entry);
  new_entry->key = key;

  // invoke any listeners associated with the key.

  for (size_t ind = 0; ind < key->owned_listeners.Size(); ind++)
    key->owned_listeners[ind]->Visit(new_entry);

  for (size_t ind = 0; ind < key->parent_listeners.Size(); ind++)
    key->parent_listeners[ind]->Visit(new_entry);

  return true;
}

ConstraintKey* ConstraintTable::LookupKey(FrameId source_frame,
                                          Exp *source_exp, bool force_create)
{
  if (m_bucket_count == 0) {
    if (force_create)
      Resize(m_min_bucket_count);
    else
      return NULL;
  }

  uint32_t key_hash = GetKeyHash(source_frame, source_exp);
  Bucket *key_bucket = &m_buckets[key_hash % m_bucket_count];

  ConstraintKey *key = key_bucket->key_begin;
  while (key) {
    if (key->frame == source_frame && key->exp == source_exp) {
      // found the key we're looking for.
      return key;
    }
    key = key->next;
  }

  if (!force_create)
    return NULL;

  // make a key for the association.
  key = track_new_single<ConstraintKey>(m_alloc);
  key->table = this;
  key->frame = source_frame;
  key->exp = source_exp;

  LinkedListInsert<ConstraintKey,__ConstraintKey_List>(&key_bucket->key_pend, key);

  // add the key to the topmost context.
  TableContext *context = m_contexts.Back();
  context->keys.PushBack(key);

  // construct any requested listeners for the key.
  for (size_t ind = 0; ind < m_listener_functions.Size(); ind++) {
    ConstraintListenerFn function = m_listener_functions[ind];
    ConstraintListener *listener = function(m_solver, key);

    if (listener)
      key->owned_listeners.PushBack(listener);
  }

  return key;
}

void ConstraintTable::AddListener(ConstraintKey *key,
                                  ConstraintListener *listener)
{
  Assert(key->table == this);

  // ignore duplicate listener inserts. any earlier insert was from an earlier
  // context and so will outlast this insert.
  if (key->owned_listeners.Contains(listener))
    return;
  if (key->parent_listeners.Contains(listener))
    return;

  key->parent_listeners.PushBack(listener);

  ParentListener info;
  info.key = key;
  info.listener = listener;

  // add the listener to the topmost context.
  TableContext *context = m_contexts.Back();
  context->listeners.PushBack(info);

  // visit the listener on any existing entries.
  ConstraintEntry *entry = key->entries_begin;
  while (entry) {
    listener->Visit(entry);
    entry = entry->key_next;
  }
}

void ConstraintTable::PushContext()
{
  TableContext *context = new TableContext();
  m_contexts.PushBack(context);
}

void ConstraintTable::PopContext()
{
  TableContext *context = m_contexts.Back();
  m_contexts.PopBack();

  // since the removed keys may be referenced by the removed entries
  // and listeners, we have to delete the entries and listeners before
  // deleting the keys.

  // remove all entries in the context list.

  for (size_t ind = 0; ind < context->entries.Size(); ind++) {
    ConstraintEntry *entry = context->entries[ind];

    size_t bucketIndex = entry->Hash() % m_bucket_count;
    Bucket *bucket = &m_buckets[bucketIndex];

    LinkedListRemove<ConstraintEntry,__ConstraintEntry_List>
      (&bucket->entry_pend, entry);
    LinkedListRemove<ConstraintEntry,__ConstraintEntry_KeyList>
      (&entry->key->entries_pend, entry);

    track_delete_single<ConstraintEntry>(m_alloc, entry);
    m_entry_count--;
  }

  // remove all listeners in the context list. do this in reverse order
  // so that for keys with multiple removed listeners we remove the most
  // recently added ones first.

  for (ssize_t ind = context->listeners.Size() - 1; ind >= 0; ind--) {
    ParentListener info = context->listeners[ind];

    Assert(info.key->parent_listeners.Back() == info.listener);
    info.key->parent_listeners.PopBack();
  }

  // remove all keys in the context list.

  for (size_t ind = 0; ind < context->keys.Size(); ind++) {
    ConstraintKey *key = context->keys[ind];

    // should have already removed all entries with this key.
    Assert(key->entries_begin == NULL);

    // should have already removed all parent listeners of this key.
    Assert(key->parent_listeners.Empty());

    // delete all listeners owned by this key.
    for (size_t lind = 0; lind < key->owned_listeners.Size(); lind++)
      delete key->owned_listeners[lind];

    size_t bucketIndex = key->Hash() % m_bucket_count;
    Bucket *bucket = &m_buckets[bucketIndex];

    LinkedListRemove<ConstraintKey,__ConstraintKey_List>(&bucket->key_pend, key);

    track_delete_single<ConstraintKey>(m_alloc, key);
  }

  // done with the context.
  delete context;
}

void ConstraintTable::GetKeys(Vector<ConstraintKey*> *keys)
{
  for (size_t ind = 0; ind < m_bucket_count; ind++) {
    ConstraintKey *key = m_buckets[ind].key_begin;

    while (key) {
      keys->PushBack(key);
      key = key->next;
    }
  }
}

void ConstraintTable::Clear()
{
  // pop every context, including the one we pushed during construction.
  while (!m_contexts.Empty())
    PopContext();

  // add back the empty initial context.
  PushContext();

  // this should have completely cleared the table.
  Assert(m_entry_count == 0);

  // free allocation for the buckets.
  if (m_buckets) {
    track_delete<Bucket>(m_alloc, m_buckets);
    m_buckets = NULL;
  }
  m_bucket_count = 0;
}

void ConstraintTable::Print() const
{
  logout << "CONSTRAINT: Table " << m_name << endl;

  for (size_t ind = 0; ind < m_bucket_count; ind++) {
    ConstraintKey *key = m_buckets[ind].key_begin;
    while (key) {
      logout << "  Key: " << key->exp << " [" << key->frame << "]" << endl;

      ConstraintEntry *entry = key->entries_begin;
      while (entry) {
        logout << "    " << entry->exp << " [" << entry->frame << "]" << endl;
        entry = entry->key_next;
      }

      key = key->next;
    }
  }
}

void ConstraintTable::Resize(size_t bucket_count)
{
  Assert(bucket_count >= m_min_bucket_count);
  Bucket *buckets = track_new<Bucket>(m_alloc, bucket_count);

  for (size_t ind = 0; ind < m_bucket_count; ind++) {
    Bucket *bucket = &m_buckets[ind];

    while (bucket->entry_begin) {
      ConstraintEntry *entry = bucket->entry_begin;
      LinkedListRemove<ConstraintEntry,__ConstraintEntry_List>
        (&bucket->entry_pend, entry);

      size_t nind = entry->Hash() % bucket_count;
      Bucket *new_bucket = &buckets[nind];
      LinkedListInsert<ConstraintEntry,__ConstraintEntry_List>
        (&new_bucket->entry_pend, entry);
    }

    while (bucket->key_begin) {
      ConstraintKey *key = bucket->key_begin;
      LinkedListRemove<ConstraintKey,__ConstraintKey_List>
        (&bucket->key_pend, key);

      size_t nind = key->Hash() % bucket_count;
      Bucket *new_bucket = &buckets[nind];
      LinkedListInsert<ConstraintKey,__ConstraintKey_List>
        (&new_bucket->key_pend, key);
    }
  }

  if (m_bucket_count)
    track_delete<Bucket>(m_alloc, m_buckets);

  m_buckets = buckets;
  m_bucket_count = bucket_count;
}

/////////////////////////////////////////////////////////////////////
// ConstraintListenerEqualityStep
/////////////////////////////////////////////////////////////////////

class ConstraintListenerEqualityStep : public ConstraintListener
{
 public:
  ConstraintListenerEqualityStep(Solver *solver, ConstraintKey *key)
    : ConstraintListener(solver, key)
  {}

  void Visit(ConstraintEntry *entry)
  {
    // ignore identities with our original key.
    if (entry->exp == m_key->exp && entry->frame == m_key->frame)
      return;

    // the key for this entry is a value we already know to be possibly
    // equal to our original key. the entry itself is a value which we may
    // may not know to already be equal.

    ConstraintTable &equal_trans = m_solver->m_constraint_equal_transitive;
    ConstraintTable &equal_step = m_solver->m_constraint_equal_step;

    bool inserted = equal_trans.Insert(m_key->frame, m_key->exp,
                                       entry->frame, entry->exp);

    if (inserted) {
      // listen for any new equalities added for the entry itself.
      ConstraintKey *entry_key =
        equal_step.LookupKey(entry->frame, entry->exp, true);
      equal_step.AddListener(entry_key, this);
    }
  }
};

ConstraintListener* MakeConstraintEqualityStep(Solver *solver, ConstraintKey *key)
{
  return new ConstraintListenerEqualityStep(solver, key);
}

/////////////////////////////////////////////////////////////////////
// ConstraintListenerLvalue
/////////////////////////////////////////////////////////////////////

inline TypeInt* GetTargetIntType(Exp *exp)
{
  if (!exp->IsDrf() && !exp->IsClobber())
    return NULL;

  Exp *target = exp->GetLvalTarget();
  Type *type = target->GetType();

  if (type)
    return type->IfInt();
  return NULL;
}

class ConstraintListenerLvalue : public ConstraintListener
{
 public:
  ConstraintListenerLvalue(Solver *solver, ConstraintKey *key)
    : ConstraintListener(solver, key)
  {}

  // check for constraints to add according to the type of exp.
  void CheckType(FrameId frame, Exp *exp)
  {
    TypeInt *type = GetTargetIntType(exp);

    if (!type)
      return;

    // restrict to non-negative values for unsigned integers.
    if (!type->IsSigned()) {
      Exp *zero = Exp::MakeInt(0);
      Bit *unsigned_test =
        Exp::MakeCompareBit(B_GreaterEqual, exp, zero);
      m_solver->AddConstraint(frame, unsigned_test);
    }

    size_t bits = type->Width() * 8;
    bool sign = type->IsSigned();

    // restrict the maximum value according to the type.
    const char *max_value = GetMaximumInteger(bits, sign);

    Exp *max_exp = Exp::MakeIntStr(max_value);
    Bit *max_test = Exp::MakeCompareBit(B_LessEqual, exp, max_exp);
    m_solver->AddConstraint(frame, max_test);
  }

  // check for uses of a field offset from NULL, e.g. &0->f.
  void CheckOffset(FrameId frame, Exp *exp)
  {
    // we don't simplify these expressions when constructing them to avoid
    // interfering with construction of Rfld expressions.
    Vector<Field*> fields;

    Exp *cur_exp = exp;
    while (true) {
      ExpFld *nexp = cur_exp->IfFld();
      if (nexp == NULL)
        return;
      fields.PushBack(nexp->GetField());

      Exp *target = nexp->GetTarget();
      if (ExpInt *ntarget = target->IfInt()) {
        long value;
        if (ntarget->GetInt(&value) && value == 0)
          break;
      }

      cur_exp = target;
    }

    size_t offset = 0;
    for (size_t ind = 0; ind < fields.Size(); ind++) {
      Field *field = fields[ind];

      // find the offset in the containing CSU type.
      String *csu_name = field->GetCSUType()->GetCSUName();
      CompositeCSU *csu = CompositeCSUCache.Lookup(csu_name);

      for (size_t find = 0; find < csu->GetFieldCount(); find++) {
        const DataField &df = csu->GetField(find);
        if (df.field == field) {
          offset += df.offset;
          break;
        }
      }

      CompositeCSUCache.Release(csu_name);
    }

    Exp *offset_exp = Exp::MakeInt(offset);
    Bit *offset_test = Exp::MakeCompareBit(B_Equal, exp, offset_exp);
    m_solver->AddConstraint(frame, offset_test);
  }

  // check for constraints to add if exp is known to be constant.
  void CheckConstant(FrameId frame, Exp *exp)
  {
    // constant exps are globals which are known to have a fixed value.
    // this will be expanded to handle exps which are known to inhabit
    // some range, or which have a known terminator position.

    Exp *target = NULL;
    Variable *var = NULL;
    if (exp->IsDrf()) {
      target = exp->AsDrf()->GetTarget();
      if (target->IsVar())
        var = target->AsVar()->GetVariable();
    }

    if (!var || !var->IsGlobal())
      return;
    Assert(target);

    // only doing scalar globals for now, not arrays.
    Type *var_type = var->GetType();
    if (!var_type || !var_type->IsInt())
      return;

    Trace *trace = Trace::MakeGlob(target);

    // check if there are writes other than in the initializer.
    // TODO: should be doing escape analysis to check for indirect writes
    // to the variable.
    EscapeAccessSet *aset = EscapeAccessCache.Lookup(trace);

    if (aset) {
      BlockPPoint init_write;
      bool found_other_write = false;

      for (size_t aind = 0; aind < aset->GetAccessCount(); aind++) {
        const EscapeAccess &access = aset->GetAccess(aind);
        if (access.kind != EAK_Write)
          continue;

        if (access.where.id->Kind() == B_Initializer &&
            access.where.id->Function() == var->GetName()) {
          init_write = access.where;
        }
        else {
          found_other_write = true;
        }
      }

      if (init_write.id && !found_other_write) {
        // variable is only written during its initializer.
        BlockMemory *init_mcfg = GetBlockMemory(init_write.id);

        const Vector<GuardAssign> *assigns =
          init_mcfg->GetAssigns(init_write.point);
        Assert(assigns);

        if (assigns->Size() == 1) {
          const GuardAssign &gts = assigns->At(0);
          Assert(gts.left == target);

          Bit *equal_bit = Exp::MakeCompareBit(B_Equal, exp, gts.right);
          m_solver->AddConstraint(frame, equal_bit);
        }
      }
    }

    EscapeAccessCache.Release(trace);
  }

  void Visit(ConstraintEntry *entry)
  {
    // we should only see new entries in an identity mapping.
    Assert(entry->key == m_key);
    Assert(entry->frame == m_key->frame);
    Assert(entry->exp == m_key->exp);

    CheckType(entry->frame, entry->exp);
    CheckOffset(entry->frame, entry->exp);
    CheckConstant(entry->frame, entry->exp);
  }
};

// listener which adds constraints on the possible values of an lvalue.
ConstraintListener* MakeConstraintLvalue(Solver *solver, ConstraintKey *key)
{
  return new ConstraintListenerLvalue(solver, key);
}

/////////////////////////////////////////////////////////////////////
// ConstraintListenerBound
/////////////////////////////////////////////////////////////////////

Exp* GetBoundEquivalent(ExpBound *bound, ExpBound *old_bound)
{
  BoundKind kind = bound->GetBoundKind();
  BoundKind old_kind = old_bound->GetBoundKind();

  if (kind != old_kind)
    return NULL;

  Exp *target = bound->GetTarget();
  Exp *old_target = old_bound->GetTarget();

  Type *type = bound->GetStrideType();
  Type *old_type = old_bound->GetStrideType();

  size_t width = type->Width();
  size_t old_width = old_type->Width();

  // require this bound's width to be an exact multiple of the old
  // bound's width. we will divide the old bound by this factor.
  if (old_width == 0 || width == 0 || width < old_width)
    return NULL;
  size_t factor = width / old_width;
  if (old_width * factor != width)
    return NULL;

  // amount to add to the old bound before dividing.
  Exp *numerator_offset = NULL;

  if (target != old_target) {
    Assert(target && old_target);

    // need to convert these to the same target by removing their
    // index expressions.
    bool failed = false;

    if (ExpIndex *ntarget = target->IfIndex()) {
      Type *element_type = ntarget->GetElementType();
      Exp *index = ntarget->GetIndex();
      target = ntarget->GetTarget();

      // offset(target[index],old_type) is equivalent to:
      // offset(target,old_type) + scaled_index.
      numerator_offset = ScaleBoundIndex(old_type, element_type, index);

      if (!numerator_offset)
        failed = true;
    }

    // only handling the case where the new bound is an index of the
    // old bound for now.
    if (target != old_target)
      failed = true;

    if (failed)
      return NULL;
  }

  // the result is (old_bound + old_offset) / factor.

  Exp *numerator = old_bound;

  if (numerator_offset)
    numerator = Exp::MakeBinop(B_Plus, numerator, numerator_offset);

  Exp *factor_exp = Exp::MakeInt(factor);

  // use exact division for offsets. we assume that pointers into buffers
  // are always aligned, though upper bounds do not need to be. note that
  // we do not require the base offset of a malloc'ed buffer to be zero,
  // so that e.g. it is possible to pad an array of 8 byte structures
  // with a 4 byte header if the buffer's base offset is -4 (or 4, 12, etc.)
  BinopKind binop = (kind == BND_Offset ? B_DivExact : B_Div);

  return Exp::MakeBinop(binop, numerator, factor_exp);
}

class ConstraintListenerBound : public ConstraintListener
{
 public:
  ConstraintListenerBound(Solver *solver, ConstraintKey *key)
    : ConstraintListener(solver, key)
  {}

  void Visit(ConstraintEntry *entry)
  {
    Assert(entry->key == m_key);
    Assert(entry->frame == m_key->frame);
    ExpBound *bound = entry->exp->AsBound();

    // this might be different than m_key->exp, as we will group bounds on
    // a buffer with bounds on different indexes of that buffer.
    Exp *target = bound->GetTarget();

    BoundKind kind = bound->GetBoundKind();
    Type *type = bound->GetStrideType();

    // the upper bound of 'this' is always at least one (would/should be
    // checked before calling a method on the value).
    if (target && target->IsDrf() && kind == BND_Upper) {
      ExpVar *var = target->AsDrf()->GetTarget()->IfVar();
      if (var && var->GetVariable()->Kind() == VK_This) {
        Type *this_type = var->GetVariable()->GetType();
        size_t count = this_type->AsPointer()->GetTargetType()->Width() / type->Width();

        Bit *test = Exp::MakeCompareBit(B_GreaterEqual, bound, Exp::MakeInt(count));

        m_solver->AddConstraint(m_key->frame, test);
      }
    }

    // ignore bounds with a base for non-offsets.
    if (target && kind != BND_Offset)
      return;

    // there should be a target iff the bound is an offset.
    Assert((target != NULL) == (kind == BND_Offset));

    if (target) {
      // check if there is an explicit upper bound on this lvalue.
      // if so add the assertion 'abs_bound - offset == explicit_bound'.
      Exp *explicit_bound = Exp::GetExplicitBound(BND_Upper, target, type);

      if (explicit_bound) {
        Exp *abs_bound = Exp::MakeBound(BND_Upper, NULL, type);
        Exp *abs_diff = Exp::MakeBinop(B_Minus, abs_bound, bound);
        Bit *test = Exp::MakeCompareBit(B_Equal, abs_diff, explicit_bound);

        m_solver->AddConstraint(m_key->frame, test);
      }

      // fall through and look for other offsets with different strides.
    }

    // compare with all other bounds on the same base buffer.
    ConstraintEntry *other_entry = m_key->entries_begin;
    while (other_entry) {
      Assert(other_entry->frame == m_key->frame);
      ExpBound *other_bound = other_entry->exp->AsBound();

      if (other_bound != bound) {
        // try to express this bound with other_bound.
        Exp *bound_equal = GetBoundEquivalent(bound, other_bound);

        if (bound_equal) {
          Bit *test = Exp::MakeCompareBit(B_Equal, bound, bound_equal);

          m_solver->AddConstraint(m_key->frame, test);
        }
        else {
          // try to express other_bound with this bound.
          Exp *other_equal = GetBoundEquivalent(other_bound, bound);

          if (other_equal) {
            Bit *test = Exp::MakeCompareBit(B_Equal, other_bound, other_equal);
            m_solver->AddConstraint(m_key->frame, test);
          }
        }
      }

      // advance for next iteration.
      other_entry = other_entry->key_next;
    }
  }
};

ConstraintListener* MakeConstraintBound(Solver *solver, ConstraintKey *key)
{
  return new ConstraintListenerBound(solver, key);
}

/////////////////////////////////////////////////////////////////////
// ConstraintListenerTerminate
/////////////////////////////////////////////////////////////////////

class ConstraintListenerTerminate : public ConstraintListener
{
 public:
  ConstraintListenerTerminate(Solver *solver, ConstraintKey *key)
    : ConstraintListener(solver, key)
  {
    ConstraintTable &buffer_read = solver->m_constraint_buffer_read;
    m_buffer_read_key = buffer_read.LookupKey(key->frame, key->exp, true);
    buffer_read.AddListener(m_buffer_read_key, this);
  }

  void Visit(ConstraintEntry *entry)
  {
    if (entry->key == m_key) {
      ExpTerminate *term_exp = entry->exp->AsTerminate();
      Assert(term_exp->GetTarget() == m_key->exp);

      Type *type = term_exp->GetStrideType();

      if (m_key->exp) {
        // found a new terminator with a base, visit all buffer reads.
        VisitAll(m_buffer_read_key);
      }
      else {
        // found a new absolute terminator. assert it is less than the
        // absolute upper bound.
        Exp *abs_bound = Exp::MakeBound(BND_Upper, NULL, type);
        Bit *less_test = Exp::MakeCompareBit(B_LessThan, term_exp, abs_bound);
        m_solver->AddConstraint(0, less_test);
      }

      return;
    }

    // should only be able to get here for buffers with base addresses.
    Assert(m_key->exp);

    Assert(entry->key == m_buffer_read_key);

    // get the stride type used for this read.
    Exp *lval = entry->exp;
    Type *type = lval->GetType();

    if (!type)
      return;

    // find any terminators with the same stride type.
    ConstraintEntry *term_entry = m_key->entries_begin;
    while (term_entry) {
      Assert(term_entry->frame == entry->frame);

      ExpTerminate *term_exp = term_entry->exp->AsTerminate();
      ExpInt *term_int = term_exp->GetTerminateInt();

      if (!term_exp->IsCompatibleStrideType(type)) {
        term_entry = term_entry->key_next;
        continue;
      }

      // make an implication: term(lval) == 0 ==> *lval == term_int.
      // this is equivalent to: term(buf) == lval - buf ==> *lval == term_int.

      // get the offset into the buffer of the lvalue.
      Exp *lval_term = term_exp->ReplaceLvalTarget(lval);

      // compare the lvalue terminator with zero.
      Exp *zero = Exp::MakeInt(0);
      Bit *term_pos = Exp::MakeCompareBit(B_Equal, lval_term, zero);

      // get the expression which is being read.
      Exp *read_target = Exp::Compose(lval, term_exp->GetTerminateTest());
      Exp *read_exp = Exp::MakeDrf(read_target);

      // get the termination test on the read expression. note that even
      // if the read expression is a pointer, we don't need to use NotEqualP
      // as the expression is being compared with a constant (i.e. NULL).
      Bit *term_test = Exp::MakeCompareBit(B_Equal, read_exp, term_int);

      // make and assert the final implication.
      Bit *implies = Bit::MakeImply(term_pos, term_test);
      m_solver->AddConstraint(entry->frame, implies);

      term_entry = term_entry->key_next;
    }
  }

 private:
  // the key which owns this listener is from m_constraint_terminate.

  // corresponding key in m_constraint_buffer_read.
  ConstraintKey *m_buffer_read_key;
};

ConstraintListener* MakeConstraintTerminate(Solver *solver, ConstraintKey *key)
{
  return new ConstraintListenerTerminate(solver, key);
}

/////////////////////////////////////////////////////////////////////
// ConstraintListenerOffset
/////////////////////////////////////////////////////////////////////

class ConstraintListenerOffset : public ConstraintListener
{
 public:
  ConstraintListenerOffset(Solver *solver, ConstraintKey *key)
    : ConstraintListener(solver, key)
  {}

  void Visit(ConstraintEntry *entry)
  {
    Assert(entry->key == m_key);

    Exp *lval = entry->exp->GetLvalTarget();
    Assert(lval);

    Variable *var = NULL;
    if (ExpVar *nlval = lval->IfVar())
      var = nlval->GetVariable();

    ConstraintEntry *old_entry = m_key->entries_begin;
    while (old_entry) {
      ConstraintEntry *cur_entry = old_entry;
      old_entry = old_entry->key_next;

      if (cur_entry == entry)
        continue;

      Exp *cur_lval = cur_entry->exp->GetLvalTarget();
      Assert(cur_lval);

      Variable *cur_var = NULL;
      if (ExpVar *ncur_lval = cur_lval->IfVar())
        cur_var = ncur_lval->GetVariable();

      // check if the lvalues can possibly alias. for now we only mark
      // different global variables as non-aliased.
      bool non_alias = false;

      if (var && var->IsGlobal() && cur_var && cur_var->IsGlobal() &&
          var != cur_var) {
        Assert(var->GetName() != cur_var->GetName());
        non_alias = true;
      }

      if (non_alias) {
        Bit *bit = Exp::MakeCompareBit(B_NotEqual,
                                       entry->exp, cur_entry->exp, NULL);
        m_solver->AddConstraint(0, bit);
      }
    }
  }
};

ConstraintListener* MakeConstraintOffset(Solver *solver, ConstraintKey *key)
{
  return new ConstraintListenerOffset(solver, key);
}

/////////////////////////////////////////////////////////////////////
// ConstraintListenerUnintUnop
/////////////////////////////////////////////////////////////////////

class ConstraintListenerUnintUnop : public ConstraintListener
{
 public:
  ConstraintListenerUnintUnop(Solver *solver, ConstraintKey *key)
    : ConstraintListener(solver, key)
  {
    m_exp = key->exp->AsUnop();

    ConstraintTable &equal_trans = m_solver->m_constraint_equal_transitive;

    m_equal_key = equal_trans.LookupKey(key->frame, m_exp->GetOperand(), true);
    equal_trans.AddListener(m_equal_key, this);
  }

  void Visit(ConstraintEntry *entry)
  {
    if (entry->key == m_key) {
      // this is the identity entry for the base unop.
      VisitAll(m_equal_key);
      return;
    }

    // nothing to do here for now.
  }

 private:
  // uninterpreted unary expression.
  ExpUnop *m_exp;

  // key with transitive equalities for the operand of this exp.
  ConstraintKey *m_equal_key;
};

ConstraintListener* MakeConstraintUnintUnop(Solver *solver, ConstraintKey *key)
{
  return new ConstraintListenerUnintUnop(solver, key);
}

/////////////////////////////////////////////////////////////////////
// ConstraintListenerUnintBinop
/////////////////////////////////////////////////////////////////////

// add to bits constraints such that left / right == result.
// if align is specified then right exactly divides left, such that
// right * result == left.
static void GetDivisionConstraints(Exp *left, long right, Exp *result,
                                   bool align, Vector<Bit*> *bits)
{
  // ignore division by negative numbers for now. TODO: probably not correctly
  // handling cases where the divisor is negative.
  if (right <= 0)
    return;

  if (right == 1) {
    // easy case.
    bits->PushBack(Exp::MakeCompareBit(B_Equal, left, result, NULL));
    return;
  }

  // get an expression for right * result.
  Exp *right_int = Exp::MakeInt(right);
  Exp *right_mul = Exp::MakeBinop(B_Mult, right_int, result);

  if (align) {
    // handle with a single equality: right * result == left.
    bits->PushBack(Exp::MakeCompareBit(B_Equal, right_mul, left));
  }
  else {
    // handle with two inequalities: right * result <= left,
    // and right * result + (right - 1) >= left.

    Exp *right_diff = Exp::MakeInt(right - 1);
    Exp *right_sum = Exp::MakeBinop(B_Plus, right_mul, right_diff);
    bits->PushBack(Exp::MakeCompareBit(B_LessEqual, right_mul, left));
    bits->PushBack(Exp::MakeCompareBit(B_GreaterEqual, right_sum, left));
  }
}

void GetBinopConstraints(ExpBinop *exp, Vector<Bit*> *bits, bool complete)
{
  // NOTE: we match against Max and Min here, even though these are modelled
  // exactly and won't be passed to the binop listener, as invariant/sufficient
  // inference also depends on these constraints and will want to get rid
  // of the max and min operations where suitable.

  FullExpInfo info;
  info.Set(exp);

  const ExpInfo &i = info.i;
  const ExpInfo &li = info.li;
  const ExpInfo &ri = info.ri;
  const ExpInfo &lli = info.lli;
  const ExpInfo &lri = info.lri;
  const ExpInfo &rli = info.rli;
  const ExpInfo &rri = info.rri;

  // TODO: Mod, BitwiseAnd, BitwiseOr, BitwiseXOr depend on the operands being
  // nonnegative, which we should be accounting for here.

  // exp0 % exp1 <= exp0
  // exp0 % exp1 < exp1

  if (i.b_kind == B_Mod) {
    bits->PushBack(Exp::MakeCompareBit(B_LessEqual, exp, li.exp, NULL));
    bits->PushBack(Exp::MakeCompareBit(B_LessThan, exp, ri.exp, NULL));
  }

  // exp0 & exp1 <= exp0
  // exp0 & exp1 <= exp1
  // (also for max)

  if (i.b_kind == B_BitwiseAnd || i.b_kind == B_Max) {
    // result is <= the first and second operands.
    bits->PushBack(Exp::MakeCompareBit(B_LessEqual, exp, li.exp, NULL));
    bits->PushBack(Exp::MakeCompareBit(B_LessEqual, exp, ri.exp, NULL));
  }

  // exp0 min exp1 >= exp0
  // exp0 min exp1 >= exp1

  if (i.b_kind == B_Min) {
    // result is >= the first and second operands.
    bits->PushBack(Exp::MakeCompareBit(B_GreaterEqual, exp, li.exp, NULL));
    bits->PushBack(Exp::MakeCompareBit(B_GreaterEqual, exp, ri.exp, NULL));
  }

  // (exp0 / exp1) * exp1 >= (exp0 - exp1 + 1)
  // exp1 * (exp0 / exp1) >= (exp0 - exp1 + 1)

  if (i.b_kind == B_Mult && li.b_kind == B_Div && ri.exp == lri.exp) {
    Exp *one = Exp::MakeInt(1);
    Exp *min_value = Exp::MakeBinop(B_Minus, lli.exp, lri.exp);
    min_value = Exp::MakeBinop(B_Plus, min_value, one);
    bits->PushBack(Exp::MakeCompareBit(B_GreaterEqual, exp, min_value));
  }

  if (i.b_kind == B_Mult && ri.b_kind == B_Div && li.exp == rri.exp) {
    Exp *one = Exp::MakeInt(1);
    Exp *min_value = Exp::MakeBinop(B_Minus, rli.exp, rri.exp);
    min_value = Exp::MakeBinop(B_Plus, min_value, one);
    bits->PushBack(Exp::MakeCompareBit(B_GreaterEqual, exp, min_value));
  }

  // (exp0 & ~exp1) >= exp0 - exp1
  // (~exp1 & exp0) >= exp0 - exp1

  if (i.b_kind == B_BitwiseAnd && ri.u_kind == U_BitwiseNot) {
    Exp *diff = Exp::MakeBinop(B_Minus, li.exp, rli.exp);
    bits->PushBack(Exp::MakeCompareBit(B_GreaterEqual, exp, diff));
  }

  if (i.b_kind == B_BitwiseAnd && li.u_kind == U_BitwiseNot) {
    Exp *diff = Exp::MakeBinop(B_Minus, ri.exp, lli.exp);
    bits->PushBack(Exp::MakeCompareBit(B_GreaterEqual, exp, diff));
  }

  if (complete) {

    // exp0 & exp1 >= 0
    // exp0 | exp1 >= 0

    if (i.b_kind == B_BitwiseAnd || i.b_kind == B_BitwiseOr) {
      if ((li.has_value && mpz_cmp_si(li.value, 0) < 0) ||
          (ri.has_value && mpz_cmp_si(ri.value, 0) < 0)) {
        // one of the operands is negative, this shouldn't be happening.
        // TODO: fix this, sort out sign issues with bitwise ops in general.
        logout << "ERROR: Bitwise operation on negative integer" << endl;
      }
      else {
        Exp *zero = Exp::MakeInt(0);
        bits->PushBack(Exp::MakeCompareBit(B_GreaterEqual, exp, zero));
      }
    }

    // (exp0 >= 0) ==> (exp0 <</>> exp1 >= 0)
    if (i.b_kind == B_ShiftLeft || i.b_kind == B_ShiftRight) {
      Exp *zero = Exp::MakeInt(0);
      Bit *left = Exp::MakeCompareBit(B_GreaterEqual, li.exp, zero);
      Bit *right = Exp::MakeCompareBit(B_GreaterEqual, exp, zero);
      bits->PushBack(Bit::MakeImply(left, right));
    }

    long right_value = 0;
    bool has_right = false;
    if (ri.has_value && mpz_fits_slong_p(ri.value)) {
      right_value = mpz_get_si(ri.value);
      has_right = true;
    }

    // exactly model left shifts by a (small nonnegative) constant.
    if (i.b_kind == B_ShiftLeft && has_right &&
        right_value >= 0 && right_value < 16) {
      Exp *new_right = Exp::MakeInt(1 << (int) right_value);
      Exp *mul_right = Exp::MakeBinop(B_Mult, li.exp, new_right);
      bits->PushBack(Exp::MakeCompareBit(B_Equal, exp, mul_right));
    }

    // exactly model division by a constant.
    if (i.b_kind == B_Div && has_right)
      GetDivisionConstraints(li.exp, right_value, exp, false, bits);
    if (i.b_kind == B_DivExact && has_right)
      GetDivisionConstraints(li.exp, right_value, exp, true, bits);

    // exactly model right shifts by a (small nonnegative) constant.
    if (i.b_kind == B_ShiftRight && has_right &&
        right_value >= 0 && right_value < 16) {
      long div_value = 1 << (int) right_value;
      GetDivisionConstraints(li.exp, div_value, exp, false, bits);
    }
  }
}

class ConstraintListenerUnintBinop : public ConstraintListener
{
 public:
  ConstraintListenerUnintBinop(Solver *solver, ConstraintKey *key)
    : ConstraintListener(solver, key)
  {
    m_exp = key->exp->AsBinop();
    Exp *left_exp = m_exp->GetLeftOperand();
    Exp *right_exp = m_exp->GetRightOperand();

    ConstraintTable &equal_trans = m_solver->m_constraint_equal_transitive;

    m_left_equal_key = equal_trans.LookupKey(key->frame, left_exp, true);
    equal_trans.AddListener(m_left_equal_key, this);

    m_right_equal_key = equal_trans.LookupKey(key->frame, right_exp, true);
    equal_trans.AddListener(m_right_equal_key, this);
  }

  void Visit(ConstraintEntry *entry)
  {
    if (entry->key == m_key) {
      // this is the identity entry for the base unop.
      VisitAll(m_left_equal_key);
      VisitAll(m_right_equal_key);

      // look for simple constraints on the binop.
      Vector<Bit*> bits;
      GetBinopConstraints(m_exp, &bits, true);

      for (size_t ind = 0; ind < bits.Size(); ind++) {
        Bit *bit = bits[ind];
        m_solver->AddConstraint(m_key->frame, bit);
      }

      return;
    }

    // look for possible constant operands to the expression.
    if (ExpInt *int_exp = entry->exp->IfInt()) {
      bool is_left = (entry->key == m_left_equal_key);
      bool is_right = (entry->key == m_right_equal_key);
      Assert(is_left || is_right);

      // this may be a constant operand to *both* binop operands if e.g.
      // the binop is 'x * x'. in this case prioritize the right operand.
      if (is_left && is_right)
        is_left = false;

      // whether we can model the operation exactly with the integer
      // substituted in.
      bool subst_model = false;

      BinopKind binop_kind = m_exp->GetBinopKind();
      Exp *left_exp = m_exp->GetLeftOperand();
      Exp *right_exp = m_exp->GetRightOperand();

      if (is_left) {
        Assert(!left_exp->IsInt());
        switch (binop_kind) {
        case B_Mult:
          subst_model = true;
          break;
        default:
          break;
        }
      }
      else {
        Assert(!right_exp->IsInt());
        switch (binop_kind) {
        case B_Mult:
        case B_Div:
        case B_ShiftLeft:
        case B_ShiftRight:
          subst_model = true;
          break;
        default:
          break;
        }
      }

      if (subst_model) {
        Bit *equal_int;
        Exp *subst_exp;

        // make an implication for the equality, e.g.:
        // (y == 5) ==> (x * y) == (x * 5).

        // the solver already knows this if the operations are modelled
        // as uninterpreted functions. adding this implied equality
        // increases precision as the two multiplications will be converted
        // differently, where one is 

        if (is_left) {
          equal_int = Exp::MakeCompareBit(B_Equal, int_exp, left_exp);
          subst_exp = Exp::MakeBinop(binop_kind, int_exp, right_exp);
        }
        else {
          equal_int = Exp::MakeCompareBit(B_Equal, int_exp, right_exp);
          subst_exp = Exp::MakeBinop(binop_kind, left_exp, int_exp);
        }

        Bit *equal_binop = Exp::MakeCompareBit(B_Equal, m_exp, subst_exp);
        Bit *imply_test = Bit::MakeImply(equal_int, equal_binop);
        m_solver->AddConstraint(m_key->frame, imply_test);
      }
    }
  }

 private:
  // uninterpreted binary expression.
  ExpBinop *m_exp;

  // keys with transitive equalities for the left/right operands of this exp.
  ConstraintKey *m_left_equal_key;
  ConstraintKey *m_right_equal_key;
};

ConstraintListener* MakeConstraintUnintBinop(Solver *solver, ConstraintKey *key)
{
  return new ConstraintListenerUnintBinop(solver, key);
}

/////////////////////////////////////////////////////////////////////
// ConstraintListenerCombineBinop
/////////////////////////////////////////////////////////////////////

class ConstraintListenerCombineBinop : public ConstraintListener
{
 public:
  ConstraintListenerCombineBinop(Solver *solver, ConstraintKey *key)
    : ConstraintListener(solver, key)
  {
    m_frame = key->frame;
    m_binop = key->exp->AsBinop()->GetBinopKind();
  }

  void Visit(ConstraintEntry *new_entry)
  {
    Exp *new_left_exp = new_entry->exp->AsBinop()->GetLeftOperand();
    Exp *new_right_exp = new_entry->exp->AsBinop()->GetRightOperand();

    ConstraintEntry *entry = m_key->entries_begin;
    while (entry) {
      if (entry == new_entry) {
        entry = entry->key_next;
        continue;
      }

      Assert(new_entry->exp != entry->exp);

      Exp *left_exp = entry->exp->AsBinop()->GetLeftOperand();
      Exp *right_exp = entry->exp->AsBinop()->GetRightOperand();

      bool shared_left = false;
      Exp *shared_exp = NULL;
      Exp *differ_exp = NULL;
      Exp *differ_exp_new = NULL;

      if (new_left_exp == left_exp) {
        shared_left = true;
        shared_exp = left_exp;
        differ_exp = right_exp;
        differ_exp_new = new_right_exp;
      }
      else if (new_right_exp == right_exp) {
        shared_left = false;
        shared_exp = right_exp;
        differ_exp = left_exp;
        differ_exp_new = new_left_exp;
      }
      else if (new_left_exp == right_exp) {
        if (IsCommutativeBinop(m_binop)) {
          shared_exp = right_exp;
          differ_exp = left_exp;
          differ_exp_new = new_right_exp;
        }
      }
      else if (new_right_exp == left_exp) {
        if (IsCommutativeBinop(m_binop)) {
          shared_exp = left_exp;
          differ_exp = right_exp;
          differ_exp_new = new_left_exp;
        }
      }

      if (shared_exp) {
        switch (m_binop) {
        case B_Mult:
          CombineMult(entry->exp, new_entry->exp,
                      shared_exp, differ_exp, differ_exp_new);
          break;
        case B_ShiftRight:
          if (shared_left)
            RightCombineShiftRight(entry->exp, new_entry->exp,
                                   shared_exp, differ_exp, differ_exp_new);
          else
            LeftCombineShiftRight(entry->exp, new_entry->exp,
                                  shared_exp, differ_exp, differ_exp_new);
          break;
        default:
          break;
        }
      }

      entry = entry->key_next;
    }
  }

  // combine two nonlinear multiplications: (exp * exp0), (exp * exp1)
  void CombineMult(Exp *old_binop, Exp *new_binop,
                   Exp *shared_exp, Exp *differ_exp, Exp *differ_exp_new)
  {
    // only handle cases where the shared expression is an unsigned lvalue.
    TypeInt *type = GetTargetIntType(shared_exp);
    if (!type || type->IsSigned())
      return;

    // the two binops can be ordered according to the differing expressions:
    // (exp0 < exp1) ==> (exp * exp0) + exp <= (exp * exp1)
    // (exp0 > exp1) ==> (exp * exp0) - exp >= (exp * exp1)
    // the equality case is handled by the base uninterpreted function.

    Bit *lt_left =
      Exp::MakeCompareBit(B_LessThan, differ_exp, differ_exp_new);
    Exp *lt_diff =
      Exp::MakeBinop(B_Plus, old_binop, shared_exp);
    Bit *lt_right =
      Exp::MakeCompareBit(B_LessThan, lt_diff, new_binop);
    Bit *lt_imply = Bit::MakeImply(lt_left, lt_right);

    Bit *gt_left =
      Exp::MakeCompareBit(B_GreaterThan, differ_exp, differ_exp_new);
    Exp *gt_diff =
      Exp::MakeBinop(B_Minus, old_binop, shared_exp);
    Bit *gt_right =
      Exp::MakeCompareBit(B_GreaterEqual, gt_diff, new_binop);
    Bit *gt_imply = Bit::MakeImply(gt_left, gt_right);

    m_solver->AddConstraint(m_frame, lt_imply);
    m_solver->AddConstraint(m_frame, gt_imply);
  }

  // combine two nonlinear right shifts: (exp >> exp0), (exp >> exp1)
  void RightCombineShiftRight(Exp *old_binop, Exp *new_binop,
                              Exp *shared_exp, Exp *differ_exp, Exp *differ_exp_new)
  {
  }

  // combine two nonlinear right shifts: (exp0 >> exp), (exp1 >> exp)
  void LeftCombineShiftRight(Exp *old_binop, Exp *new_binop,
                             Exp *shared_exp, Exp *differ_exp, Exp *differ_exp_new)
  {
    // the two binops can be ordered according to the differing expressions:
    // (exp0 <= exp1) ==> (exp0 >> exp) <= (exp1 >> exp)
    // (exp0 >= exp1) ==> (exp0 >> exp) >= (exp1 >> exp)

    Bit *le_left =
      Exp::MakeCompareBit(B_LessEqual, differ_exp, differ_exp_new);
    Bit *le_right =
      Exp::MakeCompareBit(B_LessEqual, old_binop, new_binop);
    Bit *le_imply = Bit::MakeImply(le_left, le_right);

    Bit *ge_left =
      Exp::MakeCompareBit(B_GreaterEqual, differ_exp, differ_exp_new);
    Bit *ge_right =
      Exp::MakeCompareBit(B_GreaterEqual, old_binop, new_binop);
    Bit *ge_imply = Bit::MakeImply(ge_left, ge_right);

    m_solver->AddConstraint(m_frame, le_imply);
    m_solver->AddConstraint(m_frame, ge_imply);
  }

 private:
  // frame binop applications are being collected for.
  FrameId m_frame;

  // kind of binop whose applications are being collected.
  BinopKind m_binop;
};

ConstraintListener* MakeConstraintCombineBinop(Solver *solver, ConstraintKey *key)
{
  return new ConstraintListenerCombineBinop(solver, key);
}

NAMESPACE_XGILL_END
