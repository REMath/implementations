
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

#include "callgraph.h"
#include "serial.h"
#include "mstorage.h"
#include "baked.h"
#include <imlang/storage.h>

NAMESPACE_XGILL_BEGIN

ConfigOption print_indirect_calls(CK_Flag, "print-indirect", NULL,
                                  "print generated indirect calls");

/////////////////////////////////////////////////////////////////////
// CallEdgeSet static
/////////////////////////////////////////////////////////////////////

HashCons<CallEdgeSet> CallEdgeSet::g_table;

int CallEdgeSet::Compare(const CallEdgeSet *cset0, const CallEdgeSet *cset1)
{
  TryCompareObjects(cset0->GetFunction(), cset1->GetFunction(), Variable);
  TryCompareValues((int)cset0->IsCallers(), (int)cset1->IsCallers());
  return 0;
}

CallEdgeSet* CallEdgeSet::Copy(const CallEdgeSet *cset)
{
  return new CallEdgeSet(*cset);
}

void CallEdgeSet::Write(Buffer *buf, const CallEdgeSet *cset)
{
  Assert(cset->m_edges);
  WriteMerge(buf, cset->m_function, cset->m_callers, *(cset->m_edges));
}

CallEdgeSet* CallEdgeSet::Read(Buffer *buf)
{
  Variable *function = NULL;
  bool callers = false;
  Vector<CallEdge> edges;

  ReadMerge(buf, &function, &callers, &edges);

  CallEdgeSet *res = Make(function, callers);
  if (res->GetEdgeCount() != 0)
    return res;

  for (size_t eind = 0; eind < edges.Size(); eind++)
    res->AddEdge(edges[eind]);
  return res;
}

void CallEdgeSet::WriteMerge(Buffer *buf,
                             Variable *function, bool callers,
                             const Vector<CallEdge> &edges)
{
  WriteOpenTag(buf, TAG_CallEdgeSet);
  Variable::Write(buf, function);
  WriteTagEmpty(buf, callers ? TAG_True : TAG_False);

  for (size_t eind = 0; eind < edges.Size(); eind++) {
    const CallEdge &edge = edges[eind];
    WriteOpenTag(buf, TAG_CallEdge);
    BlockPPoint::Write(buf, edge.where);
    Variable::Write(buf, edge.callee);
    if (edge.rfld_chain)
      Exp::Write(buf, edge.rfld_chain);
    WriteCloseTag(buf, TAG_CallEdge);
  }

  WriteCloseTag(buf, TAG_CallEdgeSet);
}

void CallEdgeSet::ReadMerge(Buffer *buf,
                            Variable **pfunction, bool *pcallers,
                            Vector<CallEdge> *pedges)
{
  Try(ReadOpenTag(buf, TAG_CallEdgeSet));
  while (!ReadCloseTag(buf, TAG_CallEdgeSet)) {
    switch (PeekOpenTag(buf)) {
    case TAG_Variable: {
      Try(*pfunction == NULL);
      *pfunction = Variable::Read(buf);
      break;
    }
    case TAG_True: {
      Try(ReadTagEmpty(buf, TAG_True));
      *pcallers = true;
      break;
    }
    case TAG_False: {
      Try(ReadTagEmpty(buf, TAG_False));
      *pcallers = false;
      break;
    }
    case TAG_CallEdge: {
      Try(ReadOpenTag(buf, TAG_CallEdge));

      BlockPPoint where = BlockPPoint::Read(buf);
      Variable *callee = Variable::Read(buf);
      Exp *rfld_chain = NULL;
      if (PeekOpenTag(buf) == TAG_Exp)
        rfld_chain = Exp::Read(buf);
      pedges->PushBack(CallEdge(where, callee, rfld_chain));

      Try(ReadCloseTag(buf, TAG_CallEdge));
      break;
    }
    default:
      BadTag(PeekOpenTag(buf));
    }
  }

  Try(*pfunction != NULL);
  Try(!pedges->Empty());
}

Exp* CallEdgeAddRfldExp(Exp *exp, BlockId *callee, Exp *rfld_chain)
{
  if (!rfld_chain || rfld_chain->IsEmpty())
    return exp;

  Assert(callee->Kind() == B_Function);
  Variable *this_var = Variable::Make(callee, VK_This, NULL, 0, NULL);
  Exp *this_exp = Exp::MakeVar(this_var);
  Exp *this_drf = Exp::MakeDrf(this_exp);
  Exp *this_rfld = Exp::Compose(this_drf, rfld_chain);

  return ExpReplaceExp(exp, this_drf, this_rfld);
}

Bit* CallEdgeAddRfldBit(Bit *bit, BlockId *callee, Exp *rfld_chain)
{
  if (!rfld_chain || rfld_chain->IsEmpty())
    return bit;

  Assert(callee->Kind() == B_Function);
  Variable *this_var = Variable::Make(callee, VK_This, NULL, 0, NULL);
  Exp *this_exp = Exp::MakeVar(this_var);
  Exp *this_drf = Exp::MakeDrf(this_exp);
  Exp *this_rfld = Exp::Compose(this_drf, rfld_chain);

  return BitReplaceExp(bit, this_drf, this_rfld);
}

/////////////////////////////////////////////////////////////////////
// CallEdgeSet
/////////////////////////////////////////////////////////////////////

CallEdgeSet::CallEdgeSet(Variable *function, bool callers)
  : m_function(function), m_callers(callers), m_edges(NULL)
{
  Assert(m_function);
  m_hash = m_function->Hash();
  m_hash = Hash32(m_hash, m_callers);
}

size_t CallEdgeSet::GetEdgeCount() const
{
  if (m_edges == NULL)
    return 0;
  return m_edges->Size();
}

const CallEdge& CallEdgeSet::GetEdge(size_t ind) const
{
  Assert(m_edges != NULL);
  return m_edges->At(ind);
}

void CallEdgeSet::AddEdge(const CallEdge &edge)
{
  if (m_edges == NULL)
    m_edges = new Vector<CallEdge>();

  if (!m_edges->Contains(edge))
    m_edges->PushBack(edge);
}

void CallEdgeSet::SetEdgeVersion(size_t ind, VersionId version)
{
  Assert(m_edges);
  m_edges->At(ind).where.version = version;
}

void CallEdgeSet::Print(OutStream &out) const
{
  out << "Call edge set"
      << (m_callers ? " [callers]" : " [callees]")
      << ": " << m_function << endl;

  if (m_edges != NULL) {
    for (size_t eind = 0; eind < m_edges->Size(); eind++) {
      const CallEdge &edge = m_edges->At(eind);
      out << "  " << edge.where << " -> " << edge.callee->GetName();
      if (edge.rfld_chain)
        out << " [" << edge.rfld_chain << "]";
      out << endl;
    }
  }
}

void CallEdgeSet::MarkChildren() const
{
  m_function->Mark();

  if (m_edges != NULL) {
    for (size_t eind = 0; eind < m_edges->Size(); eind++) {
      const CallEdge &edge = m_edges->At(eind);

      edge.where.id->Mark();
      edge.callee->Mark();
      if (edge.rfld_chain)
        edge.rfld_chain->Mark();
    }
  }
}

void CallEdgeSet::Persist()
{
  Assert(m_edges == NULL);
}

void CallEdgeSet::UnPersist()
{
  if (m_edges != NULL)
    delete m_edges;
}

/////////////////////////////////////////////////////////////////////
// Callgraph computation
/////////////////////////////////////////////////////////////////////

// add to the append callgraph caches the call edges resulting from the
// specified call invoking the specified callee (directly or indirectly).
void CallgraphProcessCall(BlockCFG *cfg, PEdgeCall *edge, Variable *callee,
                          Exp *rfld_chain)
{
  Assert(callee->IsGlobal());

  BlockPPoint where(cfg->GetId(), edge->GetSource(), cfg->GetVersion());
  Variable *caller = where.id->BaseVar();

  // add the caller edge to the cache.

  Vector<CallEdgeSet*> *caller_entries =
    g_pending_callers.Lookup(callee, true);
  if (caller_entries->Empty())
    caller_entries->PushBack(CallEdgeSet::Make(callee, true));

  CallEdgeSet *caller_cset = caller_entries->At(0);
  caller_cset->AddEdge(CallEdge(where, callee, rfld_chain));

  // add the callee edge to the cache.

  Vector<CallEdgeSet*> *callee_entries =
    g_pending_callees.Lookup(caller, true);
  if (callee_entries->Empty())
    callee_entries->PushBack(CallEdgeSet::Make(caller, false));

  CallEdgeSet *callee_cset = callee_entries->At(0);
  callee_cset->AddEdge(CallEdge(where, callee, rfld_chain));
}

void CallgraphProcessCFG(BlockCFG *cfg, Vector<Variable*> *callees,
                         bool *indirect)
{
  for (size_t eind = 0; eind < cfg->GetEdgeCount(); eind++) {
    PEdge *edge = cfg->GetEdge(eind);
    if (PEdgeCall *nedge = edge->IfCall()) {

      // watch out for 'direct' calls to local variables, resulting from the
      // frontend not being able to figure out the function being referred to.
      Variable *callee = nedge->GetDirectFunction();
      if (callee && callee->IsGlobal()) {
        if (!callees->Contains(callee))
          callees->PushBack(callee);
        CallgraphProcessCall(cfg, nedge, callee, NULL);
      }

      if (!callee)
        *indirect = true;
    }
  }
}

// maximum number of locations to propagate to when finding targets
// for indirect calls. this does not include the function pointer
// targets themselves.
#define FUNPTR_ESCAPE_LIMIT  100

// if trace represents a global function then get that function.
static Variable* GetTraceFunction(Trace *trace)
{
  if (trace->Kind() == TK_Glob) {
    if (ExpVar *exp = trace->GetValue()->IfVar()) {
      Variable *var = exp->GetVariable();

      if (var->Kind() == VK_Func)
        return var;
    }
  }

  return NULL;
}

class FunctionPointerEscape : public EscapeStatus
{
 public:
  BlockCFG *m_cfg;
  PEdgeCall *m_edge;
  Vector<Variable*> *m_callees;
  bool m_found;

  FunctionPointerEscape(BlockCFG *cfg, PEdgeCall *edge,
                        Vector<Variable*> *callees)
    : EscapeStatus(false, FUNPTR_ESCAPE_LIMIT),
      m_cfg(cfg), m_edge(edge), m_callees(callees), m_found(false)
  {}

  Trace* Visit(Trace *trace, bool *skip_cutoff)
  {
    // handle discovery of a specific function as the call target.
    if (Variable *function = GetTraceFunction(trace)) {
      // check to see if there is a mismatch in the number of arguments
      // between the call edge and target function.

      BlockId *callee_id = BlockId::Make(B_Function, function);
      BlockCFG *callee = GetBlockCFG(callee_id);

      bool mismatch = false;
      if (callee) {
        // count the arguments by finding the argument local with the
        // highest index.
        size_t arg_count = 0;

        const Vector<DefineVariable> *vars = callee->GetVariables();
        for (size_t ind = 0; vars && ind < vars->Size(); ind++) {
          Variable *var = vars->At(ind).var;
          if (var->Kind() == VK_Arg && var->GetIndex() >= arg_count)
            arg_count = var->GetIndex() + 1;
        }

        if (arg_count != m_edge->GetArgumentCount())
          mismatch = true;
      }

      // discard the call edge in case of a mismatch.
      if (mismatch) {
        logout << "WARNING: Discarded mismatched indirect call: "
               << m_cfg->GetId() << ": " << m_edge->GetSource()
               << ": " << function->GetName() << endl;
      }
      else {
        if (print_indirect_calls.IsSpecified())
          logout << "Indirect: " << m_cfg->GetId()
                 << ": " << m_edge->GetSource()
                 << ": " << function->GetName() << endl;

        if (!m_callees->Contains(function))
          m_callees->PushBack(function);

        CallgraphProcessCall(m_cfg, m_edge, function, NULL);
        m_found = true;
      }
    }

    Vector<Trace*> matches;
    trace->GetMatches(&matches);

    // we just want the first one, the least specific.
    Assert(matches.Size() > 0);
    Trace *res = matches[0];

    if (GetTraceFunction(res) != NULL) {
      // don't count functions against the escape propagation
      // cutoff, so that we can find any number of function pointers
      // as long as the paths to them are short.
      *skip_cutoff = true;
    }

    return res;
  }
};

// walk the class hierarchy to get all methods which might be invoked by edge
// through field from a csu or one of its subtypes. callees is the vector
// maintaining all callees of the current function, super_callees indicates
// only the callees for superclasses of type for the walk on this edge.
static void ProcessVirtualCallees(BlockCFG *cfg, PEdgeCall *edge,
                                  Vector<Variable*> *callees,
                                  Vector<Variable*> *super_callees,
                                  String *csu_name, Field *field,
                                  Exp *object, Exp *rfld_chain)
{
  // this gets somewhat tricky when the root type of the search,
  // e.g. A in 'A->f()' does not define or override the function field,
  // but inherits it from some parent B. in these cases implicit field accesses
  // should be added by the frontend to get to that parent so that
  // the call looks like 'A->b.f()'. we need to make sure the rfld chains
  // are computed so that the callees are consistent with the call site type,
  // and that we keep track of the subclass and only add targets that are in
  // A or inherit from A.

  CompositeCSU *csu = CompositeCSUCache.Lookup(csu_name);

  // add whichever function is declared for field within csu. only do the add
  // if the same callee was added by a superclass: the callee was not
  // overridden and the implementation expects a value of the superclass type.
  Variable *function = NULL;
  for (size_t ind = 0; csu && ind < csu->GetFunctionFieldCount(); ind++) {
    const FunctionField &ff = csu->GetFunctionField(ind);
    if (ff.field == field) {
      if (ff.function && !super_callees->Contains(ff.function))
        function = ff.function;
      break;
    }
  }

  if (function) {
    if (print_indirect_calls.IsSpecified())
      logout << "Indirect: " << cfg->GetId() << ": " << edge->GetSource()
             << ": " << function->GetName()
             << " [" << rfld_chain << "]" << endl;

    if (!callees->Contains(function))
      callees->PushBack(function);

    super_callees->PushBack(function);
    CallgraphProcessCall(cfg, edge, function, rfld_chain);
  }

  // find all subclasses of this type.
  Exp *empty = Exp::MakeEmpty();
  Trace *super_trace = Trace::MakeComp(empty, csu_name);

  EscapeEdgeSet *eset = EscapeBackwardCache.Lookup(super_trace);

  for (size_t eind = 0; eset && eind < eset->GetEdgeCount(); eind++) {
    Trace *target = eset->GetEdge(eind).target;

    Assert(target->Kind() == TK_Comp);
    Assert(target->GetValue()->IsFld());

    Field *sub_field = target->GetValue()->AsFld()->GetField();
    Assert(sub_field->GetType()->IsCSU() &&
           sub_field->GetType()->AsCSU()->GetCSUName() == csu_name);

    // if the object is definitely a particular subclass due to some implicit
    // field accesses, only recurse on that subclass. peel off the implicit
    // accesses as they are accounted for.
    Exp *new_object = object;
    if (object && object->IsFld()) {
      ExpFld *nobject = object->AsFld();
      if (nobject->GetField() == sub_field)
        new_object = nobject->GetTarget();
      else
        continue;
    }

    String *new_csu_name = sub_field->GetCSUType()->GetCSUName();
    Assert(new_csu_name == target->GetCSUName());

    Exp *new_rfld_chain = Exp::MakeRfld(rfld_chain, sub_field);

    ProcessVirtualCallees(cfg, edge, callees, super_callees,
                          new_csu_name, field, new_object, new_rfld_chain);
  }

  EscapeBackwardCache.Release(super_trace);

  if (function)
    super_callees->PopBack();

  CompositeCSUCache.Release(csu_name);
}

void CallgraphProcessCFGIndirect(BlockCFG *cfg, Vector<Variable*> *callees)
{
  static BaseTimer indirect_timer("cfg_indirect");
  Timer _timer(&indirect_timer);

  for (size_t eind = 0; eind < cfg->GetEdgeCount(); eind++) {
    PEdgeCall *edge = cfg->GetEdge(eind)->IfCall();
    if (!edge) continue;

    Variable *callee = edge->GetDirectFunction();
    if (callee != NULL) {
      // this is a direct call and we generated the edge for it already.
      continue;
    }

    Exp *function = edge->GetFunction();

    if (Exp *object = edge->GetInstanceObject()) {
      // virtual call through an object. we've encoded the class hierarchy
      // in the escape edges so walk this to get the possible targets.
      // along the way we need to accumulate the reverse field chains
      // to get from this object to each callee.

      // get the supertype to use from the callsite's signature.
      String *csu_name = edge->GetType()->GetCSUType()->GetCSUName();

      if (IgnoreType(csu_name)) {
        logout << "WARNING: Ignoring virtual call: " << edge << endl;
        continue;
      }

      if (!function->IsDrf() ||
          !function->AsDrf()->GetTarget()->IsFld()) {
        logout << "WARNING: Unexpected function format for virtual call:"
               << edge << endl;
        continue;
      }

      Field *field = function->AsDrf()->GetTarget()->AsFld()->GetField();
      Exp *rfld_chain = Exp::MakeEmpty();

      Vector<Variable*> super_callees;

      ProcessVirtualCallees(cfg, edge, callees, &super_callees,
                            csu_name, field, object, rfld_chain);
    }
    else {
      // indirect call through a function pointer. do an escape to propagate
      // backwards and find the possible targets.

      FunctionPointerEscape escape(cfg, edge, callees);
      Trace *source = Trace::MakeFromExp(cfg->GetId(), function);
      bool success = source && escape.FollowEscape(source);

      if (!success) {
        logout << "WARNING: Incomplete function pointer propagation: "
               << edge << endl;
      }

      if (!escape.m_found) {
        logout << "WARNING: No indirect targets found: "
               << cfg->GetId() << ": " << edge << endl;
      }
    }
  }
}

NAMESPACE_XGILL_END
