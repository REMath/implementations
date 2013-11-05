
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

#include "escape.h"
#include "serial.h"
#include "mstorage.h"
#include <imlang/storage.h>

NAMESPACE_XGILL_BEGIN

ConfigOption print_escape(CK_Flag, "print-escape", NULL,
                          "print generated escape information");

/////////////////////////////////////////////////////////////////////
// EscapeEdgeSet static
/////////////////////////////////////////////////////////////////////

HashCons<EscapeEdgeSet> EscapeEdgeSet::g_table;

int EscapeEdgeSet::Compare(const EscapeEdgeSet *eset0,
                           const EscapeEdgeSet *eset1)
{
  TryCompareObjects(eset0->GetSource(), eset1->GetSource(), Trace);
  TryCompareValues((int)eset0->IsForward(), (int)eset1->IsForward());
  return 0;
}

EscapeEdgeSet* EscapeEdgeSet::Copy(const EscapeEdgeSet *eset)
{
  return new EscapeEdgeSet(*eset);
}

void EscapeEdgeSet::Write(Buffer *buf, const EscapeEdgeSet *eset)
{
  Assert(eset->m_edges);
  WriteMerge(buf, eset->m_source, eset->m_forward, *(eset->m_edges));
}

EscapeEdgeSet* EscapeEdgeSet::Read(Buffer *buf)
{
  Trace *source = NULL;
  bool forward = false;
  Vector<EscapeEdge> edges;

  ReadMerge(buf, &source, &forward, &edges);

  EscapeEdgeSet *res = Make(source, forward);
  res->UnPersist();

  for (size_t eind = 0; eind < edges.Size(); eind++)
    res->AddEdge(edges[eind]);
  return res;
}

void EscapeEdgeSet::WriteList(Buffer *buf,
                              const Vector<EscapeEdgeSet*> &eset_list)
{
  Assert(buf->pos == buf->base);
  for (size_t ind = 0; ind < eset_list.Size(); ind++)
    Write(buf, eset_list[ind]);
}

void EscapeEdgeSet::ReadList(Buffer *buf, Vector<EscapeEdgeSet*> *eset_list)
{
  Assert(buf->pos == buf->base);
  while (buf->pos != buf->base + buf->size) {
    EscapeEdgeSet *eset = Read(buf);
    eset_list->PushBack(eset);
  }
}

void EscapeEdgeSet::WriteMerge(Buffer *buf, Trace *source, bool forward,
                               const Vector<EscapeEdge> &edges)
{
  WriteOpenTag(buf, TAG_EscapeEdgeSet);

  Trace::Write(buf, source);
  WriteTagEmpty(buf, forward ? TAG_True : TAG_False);

  for (size_t eind = 0; eind < edges.Size(); eind++) {
    const EscapeEdge &edge = edges[eind];

    WriteOpenTag(buf, TAG_EscapeEdge);

    Trace::Write(buf, edge.target);
    BlockPPoint::Write(buf, edge.where);

    if (edge.move_caller)
      WriteTagEmpty(buf, TAG_EscapeEdgeMoveCaller);
    if (edge.move_callee)
      WriteTagEmpty(buf, TAG_EscapeEdgeMoveCallee);

    WriteCloseTag(buf, TAG_EscapeEdge);
  }

  WriteCloseTag(buf, TAG_EscapeEdgeSet);
}

void EscapeEdgeSet::ReadMerge(Buffer *buf, Trace **psource, bool *pforward,
                              Vector<EscapeEdge> *pedges)
{
  Try(ReadOpenTag(buf, TAG_EscapeEdgeSet));
  while (!ReadCloseTag(buf, TAG_EscapeEdgeSet)) {
    switch (PeekOpenTag(buf)) {
    case TAG_Trace: {
      Try(*psource == NULL);
      *psource = Trace::Read(buf);
      break;
    }
    case TAG_True: {
      Try(ReadTagEmpty(buf, TAG_True));
      *pforward = true;
      break;
    }
    case TAG_False: {
      Try(ReadTagEmpty(buf, TAG_False));
      *pforward = false;
      break;
    }
    case TAG_EscapeEdge: {
      Try(ReadOpenTag(buf, TAG_EscapeEdge));

      Trace *target = Trace::Read(buf);
      BlockPPoint where = BlockPPoint::Read(buf);

      bool move_caller = false;
      bool move_callee = false;

      if (PeekOpenTag(buf) == TAG_EscapeEdgeMoveCaller) {
        move_caller = true;
        ReadTagEmpty(buf, TAG_EscapeEdgeMoveCaller);
      }
      else if (PeekOpenTag(buf) == TAG_EscapeEdgeMoveCallee) {
        move_callee = true;
        ReadTagEmpty(buf, TAG_EscapeEdgeMoveCallee);
      }

      pedges->PushBack(EscapeEdge(target, where, move_caller, move_callee));

      Try(ReadCloseTag(buf, TAG_EscapeEdge));
      break;
    }
    default:
      BadTag(PeekOpenTag(buf));
    }
  }

  Try(*psource != NULL);
  Try(!pedges->Empty());
}

/////////////////////////////////////////////////////////////////////
// EscapeEdgeSet
/////////////////////////////////////////////////////////////////////

HashCons<EscapeAccessSet> EscapeAccessSet::g_table;

EscapeEdgeSet::EscapeEdgeSet(Trace *source, bool forward)
  : m_source(source), m_forward(forward), m_edges(NULL)
{
  Assert(m_source);
  m_hash = m_source->Hash();
  m_hash = Hash32(m_hash, m_forward);
}

size_t EscapeEdgeSet::GetEdgeCount() const
{
  if (m_edges == NULL)
    return 0;
  return m_edges->Size();
}

const EscapeEdge& EscapeEdgeSet::GetEdge(size_t ind) const
{
  Assert(m_edges != NULL);
  return m_edges->At(ind);
}

void EscapeEdgeSet::AddEdge(const EscapeEdge &edge)
{
  if (m_edges == NULL)
    m_edges = new Vector<EscapeEdge>();

  if (!m_edges->Contains(edge))
    m_edges->PushBack(edge);
}

void EscapeEdgeSet::SetEdgeVersion(size_t ind, VersionId version)
{
  Assert(m_edges);
  m_edges->At(ind).where.version = version;
}

void EscapeEdgeSet::Print(OutStream &out) const
{
  out << "Edge set"
      << (m_forward ? " [forward]" : " [backward]")
      << ": " << m_source << endl;

  if (m_edges != NULL) {
    for (size_t eind = 0; eind < m_edges->Size(); eind++) {
      out << "  ";
      m_edges->At(eind).Print(out);
      out << endl;
    }
  }
}

void EscapeEdgeSet::MarkChildren() const
{
  m_source->Mark();

  for (size_t eind = 0; m_edges && eind < m_edges->Size(); eind++) {
    const EscapeEdge &edge = m_edges->At(eind);
    edge.target->Mark();
    edge.where.id->Mark();
  }
}

void EscapeEdgeSet::Persist()
{
  Assert(m_edges == NULL);
}

void EscapeEdgeSet::UnPersist()
{
  if (m_edges != NULL) {
    delete m_edges;
    m_edges = NULL;
  }
}

/////////////////////////////////////////////////////////////////////
// EscapeAccessSet static
/////////////////////////////////////////////////////////////////////

int EscapeAccessSet::Compare(const EscapeAccessSet *aset0,
                             const EscapeAccessSet *aset1)
{
  TryCompareObjects(aset0->GetValue(), aset1->GetValue(), Trace);
  return 0;
}

EscapeAccessSet* EscapeAccessSet::Copy(const EscapeAccessSet *aset)
{
  return new EscapeAccessSet(*aset);
}

void EscapeAccessSet::Write(Buffer *buf, const EscapeAccessSet *aset)
{
  Assert(aset->m_accesses);
  WriteMerge(buf, aset->m_value, *(aset->m_accesses));
}

EscapeAccessSet* EscapeAccessSet::Read(Buffer *buf)
{
  Trace *value = NULL;
  Vector<EscapeAccess> accesses;

  ReadMerge(buf, &value, &accesses);

  EscapeAccessSet *res = Make(value);
  res->UnPersist();

  for (size_t aind = 0; aind < accesses.Size(); aind++)
    res->AddAccess(accesses[aind]);
  return res;
}

void EscapeAccessSet::WriteList(Buffer *buf,
                                const Vector<EscapeAccessSet*> &aset_list)
{
  Assert(buf->pos == buf->base);
  for (size_t ind = 0; ind < aset_list.Size(); ind++)
    Write(buf, aset_list[ind]);
}

void EscapeAccessSet::ReadList(Buffer *buf,
                               Vector<EscapeAccessSet*> *aset_list)
{
  Assert(buf->pos == buf->base);
  while (buf->pos != buf->base + buf->size) {
    EscapeAccessSet *aset = Read(buf);
    aset_list->PushBack(aset);
  }
}

void EscapeAccessSet::WriteMerge(Buffer *buf, Trace *value,
                                 const Vector<EscapeAccess> &accesses)
{
  WriteOpenTag(buf, TAG_EscapeAccessSet);
  Trace::Write(buf, value);

  for (size_t aind = 0; aind < accesses.Size(); aind++) {
    const EscapeAccess &access = accesses[aind];

    WriteOpenTag(buf, TAG_EscapeAccess);
    WriteTagUInt32(buf, TAG_Kind, access.kind);
    Trace::Write(buf, access.target);
    BlockPPoint::Write(buf, access.where);
    if (access.field != NULL)
      Field::Write(buf, access.field);
    WriteCloseTag(buf, TAG_EscapeAccess);
  }

  WriteCloseTag(buf, TAG_EscapeAccessSet);
}

void EscapeAccessSet::ReadMerge(Buffer *buf, Trace **pvalue,
                                Vector<EscapeAccess> *paccesses)
{
  Try(ReadOpenTag(buf, TAG_EscapeAccessSet));
  while (!ReadCloseTag(buf, TAG_EscapeAccessSet)) {
    switch (PeekOpenTag(buf)) {
    case TAG_Trace: {
      Try(*pvalue == NULL);
      *pvalue = Trace::Read(buf);
      break;
    }
    case TAG_EscapeAccess: {
      Try(ReadOpenTag(buf, TAG_EscapeAccess));

      uint32_t kind;
      Try(ReadTagUInt32(buf, TAG_Kind, &kind));

      Trace *target = Trace::Read(buf);
      BlockPPoint where = BlockPPoint::Read(buf);

      Field *field = NULL;
      if (PeekOpenTag(buf) == TAG_Field)
        field = Field::Read(buf);

      EscapeAccess access((EscapeAccessKind)kind, target, where, field);
      paccesses->PushBack(access);

      Try(ReadCloseTag(buf, TAG_EscapeAccess));
      break;
    }
    default:
      BadTag(PeekOpenTag(buf));
    }
  }

  Try(*pvalue != NULL);
  Try(!paccesses->Empty());
}

void PrintEscapeAccessKind(OutStream &out,
                           EscapeAccessKind kind, Field *field)
{
  switch (kind) {
  case EAK_Read:
    out << "read"; break;
  case EAK_Write:
    out << "write"; break;
  case EAK_Index:
    out << "index"; break;
  case EAK_Fld:
    out << "fld"; break;
  case EAK_Rfld:
    out << "rfld"; break;
  default:
    Assert(false);
  }

  if (field)
    out << " " << field;
}

/////////////////////////////////////////////////////////////////////
// EscapeAccessSet
/////////////////////////////////////////////////////////////////////

EscapeAccessSet::EscapeAccessSet(Trace *value)
  : m_value(value), m_accesses(NULL)
{
  Assert(m_value);
  m_hash = m_value->Hash();
}

size_t EscapeAccessSet::GetAccessCount() const
{
  if (m_accesses == NULL)
    return 0;
  return m_accesses->Size();
}

const EscapeAccess& EscapeAccessSet::GetAccess(size_t ind) const
{
  Assert(m_accesses != NULL);
  return m_accesses->At(ind);
}

void EscapeAccessSet::AddAccess(const EscapeAccess &access)
{
  if (m_accesses == NULL)
    m_accesses = new Vector<EscapeAccess>();

  if (!m_accesses->Contains(access))
    m_accesses->PushBack(access);
}

void EscapeAccessSet::SetAccessVersion(size_t ind, VersionId version)
{
  Assert(m_accesses);
  m_accesses->At(ind).where.version = version;
}

void EscapeAccessSet::Print(OutStream &out) const
{
  out << "Access set: " << m_value << endl;

  if (m_accesses != NULL) {
    for (size_t aind = 0; aind < m_accesses->Size(); aind++) {
      const EscapeAccess &access = m_accesses->At(aind);

      out << "  ";
      PrintEscapeAccessKind(out, access.kind, access.field);
      out << " " << access.target << " [" << access.where << "]" << endl;
    }
  }
}

void EscapeAccessSet::MarkChildren() const
{
  m_value->Mark();

  for (size_t aind = 0; aind < m_accesses->Size(); aind++) {
    const EscapeAccess &access = m_accesses->At(aind);

    access.target->Mark();
    access.where.id->Mark();
    if (access.field)
      access.field->Mark();
  }
}

void EscapeAccessSet::Persist()
{
  Assert(m_accesses == NULL);
}

void EscapeAccessSet::UnPersist()
{
  if (m_accesses != NULL) {
    delete m_accesses;
    m_accesses = NULL;
  }
}

/////////////////////////////////////////////////////////////////////
// Escape computation
/////////////////////////////////////////////////////////////////////

static bool g_local_csus = false;
void EscapeUseLocalCSUs() { g_local_csus = true; }

// get a CSU either from in memory or the CSU cache.
static CompositeCSU* LookupCSU(String *name)
{
  if (g_local_csus) {
    CompositeCSU *csu = CompositeCSU::Make(name);
    if (csu->Kind() == CSU_Invalid) {
      // this CSU wasn't actually in memory, we just made an empty one.
      return NULL;
    }
    return csu;
  }
  else {
    CompositeCSU *csu = CompositeCSUCache.Lookup(name);
    if (!csu)
      CompositeCSUCache.Release(name);
    return csu;
  }
}

// release a CSU reference acquired via LookupCSU.
static void ReleaseCSU(String *name, CompositeCSU *csu)
{
  Assert(csu);
  if (!g_local_csus)
    CompositeCSUCache.Release(name);
}

// transforms Drf(E) into Drf(Fld(E)). gets a reference on the result.
static inline Exp* AddField(Exp *exp, Field *field)
{
  Exp *target = exp->AsDrf()->GetTarget();
  Exp *fld_target = Exp::MakeFld(target, field);

  return Exp::MakeDrf(fld_target);
}

// applies AddField to the expression in trace. gets a reference
// on the result.
static Trace* TraceAddField(Trace *trace, Field *field)
{
  Exp *new_exp = AddField(trace->GetValue(), field);

  switch (trace->Kind()) {
  case TK_Func: {
    Variable *func = trace->GetFunction();
    return Trace::MakeFunc(new_exp, func);
  }
  case TK_Glob:
    return Trace::MakeGlob(new_exp);
  case TK_Comp:
    // the trace location here should be a func or global, not comp
    Assert(false);
    return NULL;
  default:
    Assert(false);
    return NULL;
  }
}

// add the edge 'source -> target' over the direction indicated by forward
// for all trace locations which match source. if the type of the edge
// is a CSU, instead add the same edge for all fields of source and target.
static void ProcessEdge(BlockPPoint where, bool forward,
                        Trace *source, Trace *target, Type *type,
                        bool move_caller, bool move_callee)
{
  // if the assignment has a structure type then do the assignment
  // for all fields of the structure. also restrict just to Drf expressions;
  // this should always be the case unless we had frontend errors and
  // got confused.
  if (type && type->IsCSU() &&
      source->GetValue()->IsDrf() && target->GetValue()->IsDrf()) {
    String *csu_name = type->AsCSU()->GetCSUName();
    CompositeCSU *csu = LookupCSU(csu_name);
    if (!csu) return;

    for (size_t find = 0; find < csu->GetFieldCount(); find++) {
      const DataField &df = csu->GetField(find);

      Trace *new_source = TraceAddField(source, df.field);
      Trace *new_target = TraceAddField(target, df.field);

      ProcessEdge(where, forward,
                  new_source, new_target, df.field->GetType(),
                  move_caller, move_callee);
    }

    ReleaseCSU(csu_name, csu);
    return;
  }

  Vector<Trace*> matches;
  source->GetMatches(&matches);

  // fill in the edges for all locations matching the initial source.
  for (size_t mind = 0; mind < matches.Size(); mind++) {
    Trace *match = matches[mind];

    Vector<EscapeEdgeSet*> *entries = forward
      ? g_pending_escape_forward.Lookup(match, true)
      : g_pending_escape_backward.Lookup(match, true);

    if (entries->Empty())
      entries->PushBack(EscapeEdgeSet::Make(match, forward));

    EscapeEdgeSet *eset = entries->At(0);
    EscapeEdge edge(target, where, move_caller, move_callee);

    if (print_escape.IsSpecified()) {
      logout << "ESCAPE_EDGE: " << (forward ? "forward" : "backward")
             << ": " << match << ": ";
      edge.Print(logout);
      logout << endl;
    }

    eset->AddEdge(edge);
  }
}

// add an access of the specified kind for all trace locations which
// match exp/where.
static void ProcessAccess(BlockPPoint where, Exp *exp,
                          EscapeAccessKind kind, Field *field)
{
  Trace *trace = Trace::MakeFromExp(where.id, exp);

  if (trace == NULL)
    return;

  Vector<Trace*> matches;
  trace->GetMatches(&matches);

  for (size_t mind = 0; mind < matches.Size(); mind++) {
    Trace *match = matches[mind];

    Vector<EscapeAccessSet*> *entries =
      g_pending_escape_accesses.Lookup(match, true);

    if (entries->Empty())
      entries->PushBack(EscapeAccessSet::Make(match));

    EscapeAccessSet *aset = entries->At(0);

    if (print_escape.IsSpecified()) {
      logout << "ESCAPE_ACCESS: " << ": " << match << " @ " << trace << " ";
      PrintEscapeAccessKind(logout, kind, field);
      logout << " [" << where << "]" << endl;
    }

    aset->AddAccess(EscapeAccess(kind, trace, where, field));
  }
}

class ExpVisitor_Accesses : public ExpVisitor
{
 public:
  void Visit(Exp *exp)
  {
    switch (exp->Kind()) {
    case EK_Drf: {
      ExpDrf *nexp = exp->AsDrf();
      ProcessAccess(where, nexp->GetTarget(), EAK_Read, NULL);
      break;
    }
    case EK_Fld: {
      ExpFld *nexp = exp->AsFld();
      ProcessAccess(where, nexp->GetTarget(), EAK_Fld, nexp->GetField());
      break;
    }
    case EK_Rfld: {
      ExpRfld *nexp = exp->AsRfld();
      ProcessAccess(where, nexp->GetTarget(), EAK_Rfld, nexp->GetField());
      break;
    }
    case EK_Index: {
      ExpIndex *nexp = exp->AsIndex();
      ProcessAccess(where, nexp->GetTarget(), EAK_Index, NULL);
      break;
    }
    default:
      break;
    }
  }

  BlockPPoint where;
  ExpVisitor_Accesses(BlockPPoint _where)
    : ExpVisitor(VISK_All), where(_where)
  {}
};

// fill in accesses with data resulting from a read of read_exp.
static void ProcessRead(BlockPPoint where, Exp *read_exp, Type *type)
{
  // if the type is a CSU then do the read for all its fields
  if (type && type->IsCSU()) {

    // filter out reads of scalar CSU values.
    if (!read_exp->IsDrf())
      return;

    String *csu_name = type->AsCSU()->GetCSUName();
    CompositeCSU *csu = LookupCSU(csu_name);
    if (!csu) return;

    for (size_t find = 0; find < csu->GetFieldCount(); find++) {
      const DataField &df = csu->GetField(find);

      Exp *new_exp = AddField(read_exp, df.field);
      ProcessRead(where, new_exp, df.field->GetType());
    }

    ReleaseCSU(csu_name, csu);
    return;
  }

  ExpVisitor_Accesses visitor(where);
  read_exp->DoVisit(&visitor);
}

// fill in accesses with data resulting from a write to lval_exp.
static void ProcessWrite(BlockPPoint where, Exp *lval_exp, Type *type)
{
  // if the type is a CSU then do the write for all its fields
  if (type != NULL && type->Kind() == YK_CSU) {
    String *csu_name = type->AsCSU()->GetCSUName();
    CompositeCSU *csu = LookupCSU(csu_name);
    if (!csu) return;

    for (size_t find = 0; find < csu->GetFieldCount(); find++) {
      const DataField &df = csu->GetField(find);
      Exp *new_exp = Exp::MakeFld(lval_exp, df.field);
      ProcessWrite(where, new_exp, df.field->GetType());
    }

    ReleaseCSU(csu_name, csu);
    return;
  }

  ProcessAccess(where, lval_exp, EAK_Write, NULL);

  ExpVisitor_Accesses visitor(where);
  lval_exp->DoVisit(&visitor);
}

// add edges for any base classes of type to encode the class hierarchy.
// if Foo inherits from Bar, add an edge from (Foo,empty) to (Bar,empty).
// these edges are only added if Foo inherits any virtual methods from Bar.
static void ProcessBaseClasses(TypeCSU *type)
{
  String *csu_name = type->GetCSUName();
  CompositeCSU *csu = LookupCSU(csu_name);
  if (!csu) return;

  Vector<Field*> processed;

  for (size_t ind = 0; ind < csu->GetFunctionFieldCount(); ind++) {
    const FunctionField &ff = csu->GetFunctionField(ind);
    if (ff.base && !processed.Contains(ff.base)) {
      processed.PushBack(ff.base);
      String *base_name = ff.base->GetType()->AsCSU()->GetCSUName();

      // use a special ID for the base class edges, as this may be called
      // repeatedly for the same subclass.
      String *id_name = String::Make("__class_hierarchy__");
      Variable *id_var = Variable::Make(NULL, VK_Func, id_name, 0, NULL);
      BlockId *id = BlockId::Make(B_Initializer, id_var);
      BlockPPoint where(id, 0);

      Exp *empty = Exp::MakeEmpty();
      Exp *base_fld = Exp::MakeFld(empty, ff.base);

      Trace *sub_loc = Trace::MakeComp(base_fld, csu_name);
      Trace *super_loc = Trace::MakeComp(empty, base_name);

      ProcessEdge(where, true, sub_loc, super_loc, NULL, false, false);
      ProcessEdge(where, false, super_loc, sub_loc, NULL, false, false);
    }
  }

  ReleaseCSU(csu_name, csu);
}

// fill in edges with data resulting from an assignment
// of right_side to left_side at the point indicated by where.
static void ProcessAssign(BlockPPoint where,
                          Exp *left, Exp *right, Type *type)
{
  Exp *drf_left = Exp::MakeDrf(left);

  Trace *left_loc = Trace::MakeFromExp(where.id, drf_left);
  Trace *right_loc = Trace::MakeFromExp(where.id, right);

  if (left_loc == NULL || right_loc == NULL)
    return;

  ProcessEdge(where, true, right_loc, left_loc, type, false, false);
  ProcessEdge(where, false, left_loc, right_loc, type, false, false);
}

// get escape data for an argument caller_arg passed via argument callee_arg
// to callee at the point indicated by where.
static void ProcessCallArgument(BlockPPoint where, Variable *callee,
                                size_t callee_arg, Exp *caller_arg,
                                Type *type)
{
  Trace *right_loc = Trace::MakeFromExp(where.id, caller_arg);

  if (right_loc == NULL)
    return;

  Exp *arg_exp = Exp::MakeVar(NULL, VK_Arg, NULL, callee_arg, NULL);
  Exp *arg_drf = Exp::MakeDrf(arg_exp);

  Trace *left_loc = Trace::MakeFunc(arg_drf, callee);

  ProcessEdge(where, true, right_loc, left_loc, type, false, true);
  ProcessEdge(where, false, left_loc, right_loc, type, true, false);
}

// get escape data for assigning the return value of a call to callee to
// caller_ret at the point indicated by where.
static void ProcessCallReturn(BlockPPoint where, Variable *callee,
                              Exp *caller_ret, Type *type)
{
  Exp *drf_caller_ret = Exp::MakeDrf(caller_ret);

  Trace *left_loc = Trace::MakeFromExp(where.id, drf_caller_ret);

  if (left_loc == NULL)
    return;

  Exp *ret_exp = Exp::MakeVar(NULL, VK_Return, NULL, 0, NULL);
  Exp *ret_drf = Exp::MakeDrf(ret_exp);
  Trace *right_loc = Trace::MakeFunc(ret_drf, callee);

  ProcessEdge(where, true, right_loc, left_loc, type, true, false);
  ProcessEdge(where, false, left_loc, right_loc, type, false, true);
}

// get escape data for invoking an instance function call on instance_val
// at the point indicated by where.
static void ProcessCallInstance(BlockPPoint where, Variable *callee,
                                Exp *instance_val)
{
  Trace *right_loc = Trace::MakeFromExp(where.id, instance_val);

  if (right_loc == NULL)
    return;

  Exp *this_exp = Exp::MakeVar(NULL, VK_This, NULL, 0, NULL);
  Exp *this_drf = Exp::MakeDrf(this_exp);
  Trace *left_loc = Trace::MakeFunc(this_drf, callee);

  ProcessEdge(where, true, right_loc, left_loc, NULL, false, true);
  ProcessEdge(where, false, left_loc, right_loc, NULL, true, false);
}

// get all escape data for the specified CFG.
void EscapeProcessCFG(BlockCFG *cfg)
{
  // if there is a 'this' variable then we might need to add edges for
  // the vtable entry on this function.
  if (cfg->GetId()->Kind() == B_Function) {
    TypeCSU *this_type = NULL;
    const Vector<DefineVariable> *vars = cfg->GetVariables();

    if (vars) {
      // scan for both 'this' and the function variable itself.
      Variable *func_var = NULL;

      for (size_t vind = 0; vind < vars->Size(); vind++) {
        const DefineVariable &dv = vars->At(vind);
        if (dv.var->Kind() == VK_This) {
          Assert(this_type == NULL);
          if (TypePointer *ptr_type = dv.type->IfPointer())
            this_type = ptr_type->GetTargetType()->IfCSU();
        }
        if (dv.var->Kind() == VK_Func) {
          Assert(func_var == NULL);
          Assert(dv.var->GetName() == cfg->GetId()->Function());
          func_var = dv.var;
        }
      }

      BlockPPoint where(cfg->GetId(), cfg->GetEntryPoint(), cfg->GetVersion());

      Assert(func_var);
      if (this_type)
        ProcessBaseClasses(this_type);
    }
  }

  BlockId *id = cfg->GetId();
  for (size_t eind = 0; eind < cfg->GetEdgeCount(); eind++) {
    PEdge *edge = cfg->GetEdge(eind);

    // get the identifier for the source of this edge.
    BlockPPoint where(id, edge->GetSource(), cfg->GetVersion());

    switch (edge->Kind()) {
    case EGK_Skip:
      break;
    case EGK_Assume: {
      PEdgeAssume *nedge = edge->AsAssume();
      ProcessRead(where, nedge->GetCondition(), NULL);
      break;
    }
    case EGK_Assign: {
      PEdgeAssign *nedge = edge->AsAssign();
      Type *type = nedge->GetType();
      Exp *left_side = nedge->GetLeftSide();
      Exp *right_side = nedge->GetRightSide();

      ProcessWrite(where, left_side, type);
      ProcessRead(where, right_side, type);
      ProcessAssign(where, left_side, right_side, type);

      break;
    }
    case EGK_Call: {
      PEdgeCall *nedge = edge->AsCall();

      ExpVisitor_Accesses visitor(where);
      if (nedge->GetInstanceObject())
        nedge->GetInstanceObject()->DoVisit(&visitor);
      else
        nedge->GetFunction()->DoVisit(&visitor);

      TypeFunction *type = nedge->GetType();

      Exp *retval = nedge->GetReturnValue();
      if (retval != NULL) {
        Type *ret_type = type->GetReturnType();
        ProcessWrite(where, retval, ret_type);
      }

      for (size_t aind = 0; aind < nedge->GetArgumentCount(); aind++) {
        Exp *arg = nedge->GetArgument(aind);

        Type *arg_type = type->GetArgumentType(aind);
        ProcessRead(where, arg, arg_type);
      }

      Variable *callee = nedge->GetDirectFunction();
      if (callee != NULL)
        EscapeProcessCall(cfg, nedge, callee);

      break;
    }
    case EGK_Loop:
    case EGK_Assembly:
    case EGK_Annotation:
      break;
    default:
      Assert(false);
    }
  }
}

void EscapeProcessCall(BlockCFG *cfg, PEdgeCall *edge, Variable *callee)
{
  BlockPPoint where(cfg->GetId(), edge->GetSource(), cfg->GetVersion());
  TypeFunction *type = edge->GetType();

  Exp *return_val = edge->GetReturnValue();
  if (return_val) {
    Type *ret_type = type->GetReturnType();
    ProcessCallReturn(where, callee, return_val, ret_type);
  }

  Exp *instance_val = edge->GetInstanceObject();
  if (instance_val) {
    // type is not relevant as this is always a pointer assignment.
    ProcessCallInstance(where, callee, instance_val);
  }

  for (size_t aind = 0; aind < edge->GetArgumentCount(); aind++) {
    Exp *arg = edge->GetArgument(aind);

    Type *arg_type = type->GetArgumentType(aind);
    ProcessCallArgument(where, callee, aind, arg, arg_type);
  }
}

/////////////////////////////////////////////////////////////////////
// EscapeStatus
/////////////////////////////////////////////////////////////////////

EscapeStatus::EscapeStatus(bool forward, size_t cutoff)
  : m_forward(forward), m_cutoff(cutoff), m_cutoff_reached(false)
{}

// remove any context from the specified trace location. no escape edges
// in the cache have context on either the source or target.
static Trace* StripContext(Trace *trace)
{
  // handle cases where there is no context information to strip.
  if (trace->Kind() != TK_Func || trace->GetContextCount() == 0)
    return trace;

  Exp *exp = trace->GetValue();
  Variable *function = trace->GetFunction();
  return Trace::MakeFunc(exp, function);
}

// for the specified escape edge with source at trace, combine the
// context in trace with the edge target to get the result of
// following that edge.
static Trace* CombineContext(Trace *trace, const EscapeEdge &edge)
{
  // get the amount of context information we started with.
  size_t count = 0;
  if (trace->Kind() == TK_Func)
    count = trace->GetContextCount();

  // check if the context information is incompatible. this happens if we
  // are moving back into a caller context but the specified call site
  // is incompatible with our base context information.
  if (edge.move_caller && count) {
    if (trace->GetContext(count - 1) != edge.where)
      return NULL;
  }

  // no context information to add to non-function targets.
  if (edge.target->Kind() != TK_Func)
    return edge.target;

  Vector<BlockPPoint> context;

  // get any base context information for the original trace location.
  for (size_t ind = 0; ind < count; ind++) {
    BlockPPoint cpoint = trace->GetContext(ind);

    // strip the last context if we are moving into the caller.
    if (edge.move_caller && ind == count - 1) {
      Assert(cpoint == edge.where);
      continue;
    }

    context.PushBack(cpoint);
  }

  // add a new context if we are moving into a callee.
  if (edge.move_callee)
    context.PushBack(edge.where);

  Exp *exp = edge.target->GetValue();
  Variable *function = edge.target->GetFunction();
  return Trace::MakeFunc(exp, function, context);
}

bool EscapeStatus::FollowEscape(Trace *source)
{
  if (m_cutoff_reached)
    return false;

  EscapeStackEdge edge;
  RecursiveEscape(source, edge);

  return !m_cutoff_reached;
}

void EscapeStatus::RecursiveEscape(Trace *source, const EscapeStackEdge &prev)
{
  Assert(!m_cutoff_reached);

  // check if we have seen this trace before.
  if (m_visited.Lookup(source))
    return;

  bool skip_cutoff = false;
  Trace *new_source = Visit(source, &skip_cutoff);
  if (new_source == NULL)
    return;

  Vector<EscapeStackEdge> *entries = m_visited.Lookup(new_source, true);

  // check if our initial trace simplified to another we have seen before.
  if (!entries->Empty())
    return;

  entries->PushBack(prev);

  if (m_cutoff && !skip_cutoff) {
    m_cutoff--;
    if (m_cutoff == 0) {
      m_cutoff_reached = true;
      return;
    }
  }

  Cache_EscapeEdgeSet &cache =
    m_forward ? EscapeForwardCache : EscapeBackwardCache;

  Trace *strip_trace = StripContext(new_source);
  EscapeEdgeSet *eset = cache.Lookup(strip_trace);

  if (eset != NULL) {
    for (size_t eind = 0; eind < eset->GetEdgeCount(); eind++) {
      const EscapeEdge &edge = eset->GetEdge(eind);
      Trace *new_target = CombineContext(new_source, edge);

      EscapeStackEdge next(new_source, edge);
      m_stack.PushBack(next);

      if (new_target)
        RecursiveEscape(new_target, next);

      m_stack.PopBack();

      if (m_cutoff_reached)
        break;
    }
  }

  cache.Release(strip_trace);
}

void EscapeStatus::PrintEscapeStack()
{
  logout << "Escape Stack:" << endl;
  for (size_t ind = 0; ind < m_stack.Size(); ind++)
    m_stack[ind].Print(logout);
}

NAMESPACE_XGILL_END
