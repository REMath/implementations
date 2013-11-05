
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

#include "path.h"
#include "checker.h"
#include "propagate.h"

#include <infer/expand.h>
#include <util/xml.h>

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// DisplayValue
/////////////////////////////////////////////////////////////////////

DisplayValue::DisplayValue()
  : m_lval(NULL), m_kind(NULL), m_lval_use(NULL),
    m_rval(NULL), m_newval(NULL),
    m_bound_kind(BND_Invalid), m_bound_type(NULL), m_force_display(false)
{}

void DisplayValue::WriteXML(Buffer *buf)
{
  Assert(m_lval);
  Assert(m_rval);

  if (!m_force_display) {
    if (!strcmp(m_rval, "*") && !m_newval)
      return;
  }

  WriteXMLOpenTag(buf, "value");

  static Buffer scratch_buf;
  BufferOutStream out(&scratch_buf);

  Exp *print_exp = m_lval;

  if (m_kind)
    print_exp = m_kind->ReplaceLvalTarget(print_exp);

  switch (m_bound_kind) {
  case BND_Invalid:
    print_exp->PrintUI(out, false); break;
  default:
    Assert(m_bound_type);
    out << BoundString(m_bound_kind) << "(";
    print_exp->PrintUI(out, false);
    out << "," << m_bound_type << ")";
  }

  WriteXMLTagString(buf, "lval", out.Base());
  scratch_buf.Reset();

  WriteXMLTagString(buf, "rval", m_rval);
  if (m_newval)
    WriteXMLTagString(buf, "newval", m_newval);

  WriteXMLCloseTag(buf, "value");
}

/////////////////////////////////////////////////////////////////////
// DisplayPoint
/////////////////////////////////////////////////////////////////////

// mapper for constructing lvalues that can be exported to the UI.
class DisplayMapper : public ExpMapper
{
public:
  DisplayMapper()
    : ExpMapper(VISK_All, WIDK_Drop)
  {}

  Exp* Map(Exp *exp, Exp *old)
  {
    if (exp == NULL)
      return NULL;

    if (ExpClobber *nexp = exp->IfClobber()) {
      Exp *target = nexp->GetOverwrite();
      Exp *new_target = target->DoMap(this);

      if (!new_target)
        return NULL;

      if (Exp *kind = nexp->GetValueKind())
        return kind->ReplaceLvalTarget(new_target);
      return Exp::MakeDrf(new_target);
    }

    if (exp->IsLvalue() || exp->IsRvalue())
      return exp;

    return NULL;
  }
};

DisplayPoint::DisplayPoint()
  : m_index(0), m_frame(NULL), m_cfg_point(0),
    m_line_text(NULL), m_highlight(false)
{}

DisplayValue& DisplayPoint::GetDisplayValue(Exp *lval, Exp *kind,
                                            BoundKind bound_kind,
                                            Type *bound_type)
{
  // we should already have a valid display lvalue. double check.
  DisplayMapper mapper;
  Exp *new_lval = lval->DoMap(&mapper);
  Assert(new_lval == lval);

  if (!kind && bound_kind == BND_Invalid) {
    // if the lvalue is a pointer then make this an offset anyways.
    if (Type *type = lval->GetType()) {
      if (TypePointer *ntype = type->IfPointer()) {
        bound_kind = BND_Offset;
        bound_type = ntype->GetTargetType();
      }
    }
  }

  for (size_t ind = 0; ind < m_values.Size(); ind++) {
    if (m_values[ind].m_lval == lval &&
        m_values[ind].m_kind == kind &&
        m_values[ind].m_bound_kind == bound_kind &&
        m_values[ind].m_bound_type == bound_type) {
      return m_values[ind];
    }
  }

  m_values.PushBack(DisplayValue());
  DisplayValue &val = m_values.Back();

  val.m_lval = lval;
  val.m_kind = kind;
  val.m_bound_kind = bound_kind;
  val.m_bound_type = bound_type;

  return val;
}

void DisplayPoint::WriteXML(Buffer *buf)
{
  Assert(m_index);
  Assert(m_frame);
  Assert(m_cfg_point);

  WriteXMLOpenTag(buf, "point");
  WriteXMLTagInt(buf, "pointindex", m_index);

  BlockCFG *cfg = m_frame->m_cfg;

  Location *begin_loc = cfg->GetBeginLocation();
  Location *end_loc = cfg->GetEndLocation();
  Location *loc = cfg->GetPointLocation(m_cfg_point);

  if (loc->FileName() == begin_loc->FileName() &&
      loc->Line() >= begin_loc->Line() &&
      loc->Line() <= end_loc->Line()) {
    WriteXMLTagInt(buf, "line", loc->Line());
  }
  else {
    WriteXMLTagInt(buf, "line", begin_loc->Line());
  }

  WriteXMLTagString(buf, "linetext", m_line_text);

  if (m_highlight)
    WriteXMLTagInt(buf, "highlight", 1);

  for (size_t ind = 0; ind < m_values.Size(); ind++)
    m_values[ind].WriteXML(buf);

  WriteXMLCloseTag(buf, "point");
}

/////////////////////////////////////////////////////////////////////
// DisplayFrame
/////////////////////////////////////////////////////////////////////

DisplayFrame::DisplayFrame()
  : m_index(0), m_cfg(NULL), m_begin_point(0), m_end_point(0),
    m_main_text(NULL), m_where_text(NULL), m_callee_frame(0), m_next_frame(0)
{}

void DisplayFrame::WriteXML(Buffer *buf)
{
  Assert(m_index);
  Assert(m_cfg);
  Assert(m_main_text);
  Assert(m_where_text);

  WriteXMLOpenTag(buf, "frame");

  WriteXMLTagInt(buf, "frameindex", m_index);
  WriteXMLTagInt(buf, "beginpoint", m_begin_point);
  WriteXMLTagInt(buf, "endpoint", m_end_point);

  // write the text name of the frame's CFG.

  BlockId *id = m_cfg->GetId();

  if (id->Kind() == B_Loop)
    WriteXMLTagString(buf, "text", id->LoopName());
  else
    WriteXMLTagString(buf, "text", id->BaseVar()->GetSourceName()->Value());

  Location *begin_location = m_cfg->GetBeginLocation();
  Location *end_location = m_cfg->GetEndLocation();

  String *begin_file = begin_location->FileName();
  String *end_file = end_location->FileName();

  if (begin_file != end_file) {
    logout << "ERROR: Conflicting filenames within function: "
           << m_cfg->GetId() << endl;
    end_location = begin_location;
  }

  WriteXMLTagString(buf, "file", begin_file->Value());
  WriteXMLTagInt(buf, "beginline", begin_location->Line());
  WriteXMLTagInt(buf, "endline", end_location->Line());

  WriteXMLTagString(buf, "maintext", m_main_text);
  WriteXMLTagString(buf, "wheretext", m_where_text);

  if (m_callee_frame)
    WriteXMLTagInt(buf, "framechild", m_callee_frame);
  if (m_next_frame)
    WriteXMLTagInt(buf, "framenext", m_next_frame);

  for (size_t ind = 0; ind < m_annotations.Size(); ind++)
    WriteXMLTagString(buf, "annotation", m_annotations[ind]);

  for (size_t ind = 0; ind < m_annotation_hooks.Size(); ind++) {
    const AnnotationHook &hook = m_annotation_hooks[ind];
    WriteXMLOpenTag(buf, "hook");
    WriteXMLTagString(buf, "text", hook.m_text);
    WriteXMLTagString(buf, "name", hook.m_name);
    WriteXMLCloseTag(buf, "hook");
  }

  // the last hook is the special 'point' hook for annotating an
  // intermediate point in a function.

  static Buffer scratch_buf;
  BufferOutStream point_out(&scratch_buf);
  point_out << "point ";

  if (id->Kind() == B_Loop)
    point_out << id->Loop()->Value() << " ";
  else
    point_out << "pre ";

  point_out << id->BaseVar()->GetName()->Value();

  WriteXMLOpenTag(buf, "hook");
  WriteXMLTagString(buf, "text", "PointAssert");
  WriteXMLTagString(buf, "name", point_out.Base());
  WriteXMLCloseTag(buf ,"hook");

  scratch_buf.Reset();

  WriteXMLCloseTag(buf, "frame");
}

/////////////////////////////////////////////////////////////////////
// DisplayPath
/////////////////////////////////////////////////////////////////////

DisplayPath::DisplayPath()
  : m_emitted_xml(false), m_name(NULL)
{}

DisplayPath::~DisplayPath()
{
  for (size_t ind = 0; ind < m_buffers.Size(); ind++)
    delete m_buffers[ind];

  for (size_t ind = 0; ind < m_frames.Size(); ind++)
    delete m_frames[ind];

  for (size_t ind = 0; ind < m_points.Size(); ind++)
    delete m_points[ind];
}

void DisplayPath::WriteXML(Buffer *buf)
{
  Assert(!m_frame_roots.Empty());
  Assert(!m_emitted_xml);
  m_emitted_xml = true;

  WriteXMLOpenTag(buf, "path");

  if (m_name)
    WriteXMLTagString(buf, "name", m_name);

  for (size_t ind = 0; ind < m_frames.Size(); ind++)
    m_frames[ind]->WriteXML(buf);

  for (size_t ind = 0; ind < m_points.Size(); ind++)
    m_points[ind]->WriteXML(buf);

  for (size_t ind = 0; ind < m_frame_roots.Size(); ind++)
    WriteXMLTagInt(buf, "frameindex", m_frame_roots[ind]);

  WriteXMLCloseTag(buf, "path");
}

DisplayFrame* DisplayPath::MakeFrame(CheckerFrame *chk_frame,
                                     PPoint cfg_point)
{
  Solver *solver = chk_frame->State()->GetSolver();

  DisplayFrame *disp_frame = new DisplayFrame();
  m_frames.PushBack(disp_frame);
  disp_frame->m_index = m_frames.Size();

  BlockMemory *mcfg = chk_frame->Memory();
  BlockCFG *cfg = mcfg->GetCFG();
  disp_frame->m_cfg = cfg;

  // find the propagation to use for this display frame. the propagations for
  // the checker frame are listed starting at the bottom of the checker stack
  // (later in the CFG), so visit them in reverse order.
  CheckerPropagate *propagate = NULL;

  for (ssize_t ind = chk_frame->m_display_propagate.Size() - 1;
       ind >= 0; ind--) {
    propagate = chk_frame->m_display_propagate[ind];

    if (propagate->m_point >= cfg_point)
      break;
  }

  // the checker frame might not have any propagations attached, if we bailed
  // out after constructing the frame.
  PPoint end_point = propagate ? propagate->m_point : chk_frame->EndPoint();

  // make sure the assignment traces a path from the start to the end point.
  solver->AsnCheckPointReached(chk_frame->Id(), cfg_point);
  solver->AsnCheckPointReached(chk_frame->Id(), end_point);

  // fill in the main/where text from the propagation.

  if (propagate && propagate->m_where) {
    Location *location = cfg->GetPointLocation(propagate->m_point);

    if (propagate->m_base_bit) {
      BufferOutStream main_out(NewBuffer());
      main_out << "Assert [" << location->Line() << "] :: ";
      propagate->m_base_bit->PrintUI(main_out, true);
      disp_frame->m_main_text = main_out.Base();
    }
    else {
      disp_frame->m_main_text = "<None>";
    }

    BufferOutStream where_out(NewBuffer());
    propagate->m_where->PrintUI(where_out);
    disp_frame->m_where_text = where_out.Base();
  }
  else {
    disp_frame->m_main_text = "<None>";
    disp_frame->m_where_text = "<None>";
  }

  // get the point we will start the path from. this is normally the initial
  // point we were given, but for postconditions the call/loop invocation
  // is also included. this means the call/loop edge will end up in both the
  // before/after display frames for the call/loop.
  PPoint start_point = cfg_point;

  if (propagate && propagate->m_where) {
    if (WherePostcondition *nwhere = propagate->m_where->IfPostcondition())
      start_point = nwhere->GetPoint();
  }

  // get all assumptions used for the block. we will extract and display all
  // relevant annotations from here.
  Vector<AssumeInfo> assume_list;
  BlockSummary::GetAssumedBits(mcfg, 0, &assume_list);

  // add the baseline annotation hook. for functions this is a precondition,
  // for loops a loop invariant.
  WherePrecondition *base_where = new WherePrecondition(mcfg, NULL);
  AddHook(disp_frame, base_where);
  delete base_where;

  // add any precondition annotations for the frame.
  AddAnnotations(disp_frame, assume_list, 0, NULL);

  // construct all the points traversed in this display frame.
  // walk the assignment-generated path from the start point we have
  // until we reach the end point of the propagation.

  PPoint cur_cfg_point = start_point;
  while (true) {
    DisplayPoint *next_point = MakePoint(chk_frame, cur_cfg_point);
    next_point->m_frame = disp_frame;

    // update the begin/end points for the frame.
    if (!disp_frame->m_begin_point)
      disp_frame->m_begin_point = next_point->m_index;
    disp_frame->m_end_point = next_point->m_index;

    // make sure we don't skip past the propagate's end point.
    Assert(cur_cfg_point <= end_point);

    PEdge *edge = solver->AsnEdgeTaken(chk_frame->Id(), cur_cfg_point, false);

    if (!edge) {
      Assert(cur_cfg_point == end_point);
      break;
    }

    // add hooks for invariants on any types or globals used by the edge.
    Vector<Exp*> lval_list;
    LvalListVisitor visitor(&lval_list);
    edge->DoVisit(&visitor);

    for (size_t lind = 0; lind < lval_list.Size(); lind++) {
      Exp *lval = lval_list[lind];

      if (ExpFld *nlval = lval->IfFld()) {
        TypeCSU *csu_type = nlval->GetField()->GetCSUType();
        if (disp_frame->m_type_hooks.Contains(csu_type))
          continue;

        WhereInvariant *invariant_where =
          new WhereInvariant(csu_type, NULL, NULL);
        AddHook(disp_frame, invariant_where);
        delete invariant_where;

        disp_frame->m_type_hooks.PushBack(csu_type);
      }

      if (ExpVar *nlval = lval->IfVar()) {
        Variable *var = nlval->GetVariable();
        if (!var->IsGlobal() || disp_frame->m_global_hooks.Contains(var))
          continue;

        WhereInvariant *invariant_where = new WhereInvariant(NULL, var, NULL);
        AddHook(disp_frame, invariant_where);
        delete invariant_where;

        disp_frame->m_global_hooks.PushBack(var);
      }
    }

    if (cur_cfg_point == end_point) {
      // finished generating points for the desired path.
      break;
    }

    // if this is a call or loop then add a hook for postconditions or
    // invariants from it.
    if (edge->IsCall() || edge->IsLoop()) {
      WherePostcondition *post_where =
        new WherePostcondition(chk_frame, cur_cfg_point, NULL);
      AddHook(disp_frame, post_where);
      delete post_where;
    }

    // add any assert/assume/postcondition annotations for this point.
    AddAnnotations(disp_frame, assume_list, cur_cfg_point, edge);

    cur_cfg_point = edge->GetTarget();
  }

  disp_frame->m_type_hooks.Clear();
  disp_frame->m_global_hooks.Clear();

  // make sure the frame contains at least one point.
  Assert(disp_frame->m_begin_point);
  Assert(disp_frame->m_end_point);

  size_t root_count = m_frame_roots.Size();

  // check if there is a callee to explore at the point we stopped.
  // this also covers additional loop iterations at the exit point of
  // a loop body.
  if (CheckerFrame *callee_frame = chk_frame->GetCalleeFrame(cur_cfg_point)) {
    PPoint entry_point = callee_frame->CFG()->GetEntryPoint();

    DisplayFrame *disp_callee_frame = MakeFrame(callee_frame, entry_point);
    disp_frame->m_callee_frame = disp_callee_frame->m_index;
  }

  // check if there is a return point after any callee frame.
  if (chk_frame->EndPoint() > cur_cfg_point) {
    // should not have had any root frames added by the callee,
    // so that the return site is the next point in the path.
    Assert(m_frame_roots.Size() == root_count);

    PEdge *edge = cfg->GetSingleOutgoingEdge(cur_cfg_point);
    PPoint return_point = edge->GetTarget();

    DisplayFrame *disp_next_frame = MakeFrame(chk_frame, return_point);
    disp_frame->m_next_frame = disp_next_frame->m_index;
  }

  // check if there is a disconnected heap read frame after this point.
  if (chk_frame->EndPoint() == cur_cfg_point) {
    if (CheckerFrame *heap_frame = chk_frame->GetHeapSuccessorFrame()) {
      CheckerFrame *heap_root = heap_frame->GetPathRoot(false);
      PPoint entry_point = heap_root->CFG()->GetEntryPoint();

      DisplayFrame *disp_heap_frame = MakeFrame(heap_root, entry_point);
      m_frame_roots.PushBack(disp_heap_frame->m_index);
    }
  }

  return disp_frame;
}

void DisplayPath::AddHook(DisplayFrame *frame, Where *where)
{
  Assert(where->GetBit() == NULL);
  AnnotationHook hook;

  BufferOutStream text_out(NewBuffer());
  where->PrintUI(text_out);
  hook.m_text = text_out.Base();

  BufferOutStream name_out(NewBuffer());
  where->PrintHook(name_out);
  hook.m_name = name_out.Base();

  frame->m_annotation_hooks.PushBack(hook);
}

void DisplayPath::AddAnnotations(DisplayFrame *frame,
                                 const Vector<AssumeInfo> &assume_list,
                                 PPoint point, PEdge *edge)
{
  // scan for all annotated assumptions matching the specified point.
  for (size_t ind = 0; ind < assume_list.Size(); ind++) {
    const AssumeInfo &info = assume_list[ind];

    if (!info.annot || info.point != point)
      continue;

    // the same annotation CFG might be added multiple times for invariants
    // (e.g. when multiple objects of the same type are accessed).
    // only report each annotation once.
    bool duplicate = false;
    if (!info.point) {
      for (size_t pind = 0; pind < ind; pind++) {
        if (assume_list[pind].annot == info.annot)
          duplicate = true;
      }
    }
    if (duplicate)
      continue;

    Bit *bit = BlockMemory::GetAnnotationBit(info.annot);
    Assert(bit);

    // stream to store the annotation text.
    BufferOutStream out(NewBuffer());

    switch (info.annot->GetAnnotationKind()) {

    case AK_Precondition:
    case AK_PreconditionAssume: {
      Assert(point == 0);

      out << "Precondition :: ";
      bit->PrintUI(out, true);

      break;
    }

    case AK_Assert:
    case AK_Assume: {
      Assert(point);
      Location *loc = frame->m_cfg->GetPointLocation(point);

      out << "Assert [" << loc->Line() << "] :: ";
      bit->PrintUI(out, true);

      break;
    }

    case AK_Postcondition:
    case AK_PostconditionAssume: {
      Assert(point);
      Location *loc = frame->m_cfg->GetPointLocation(point);

      out << "Postcondition [";

      PEdgeCall *nedge = edge->AsCall();
      Exp *function = nedge->GetFunction();
      function->PrintUI(out, true);
      out << ":" << loc->Line() << "] :: ";
      bit->PrintUI(out, true);

      // for indirect calls, add in the name of the callee. get a prettier
      // function name for the callee by stripping its argument info.
      // GetSourceName isn't good enough by itself as for virtual members
      // all the callees have the same source name. TODO: fix hack.
      if (nedge->GetDirectFunction() == NULL) {
        char *new_name = strdup(info.annot->GetId()->Function()->Value());
        if (char *paren = strchr(new_name, '('))
          *paren = 0;
        out << " for " << new_name;
        free(new_name);
      }

      break;
    }

    case AK_Invariant:
    case AK_InvariantAssume: {
      Assert(point == 0);

      switch (info.annot->GetId()->Kind()) {
      case B_AnnotationInit:
        out << "Invariant :: ";
        break;
      case B_AnnotationComp:
        out << "TypeInvariant ["
            << info.annot->GetId()->Function()->Value() << "] :: ";
        break;
      default:
        Assert(false);
      }

      bit->PrintUI(out, true);
      break;
    }

    default:
      Assert(false);
    }

    frame->m_annotations.PushBack(out.Base());
  }
}

DisplayPoint* DisplayPath::MakePoint(CheckerFrame *chk_frame, PPoint cfg_point)
{
  Solver *solver = chk_frame->State()->GetSolver();

  DisplayPoint *point = new DisplayPoint();
  m_points.PushBack(point);
  point->m_index = m_points.Size();
  point->m_cfg_point = cfg_point;

  FrameId solver_frame = chk_frame->Id();
  BlockMemory *mcfg = chk_frame->Memory();

  // fill in the line text for the outgoing edge from the point.

  PEdge *edge = solver->AsnEdgeTaken(solver_frame, cfg_point, false);

  BufferOutStream line_out(NewBuffer());

  if (edge) {
    edge->PrintUI(line_out);
    line_out << ";";
  }
  else {
    BlockId *id = mcfg->GetId();
    if (id->Kind() == B_Loop) {
      line_out << "finish(" << id->LoopName() << ");";
    }
    else {
      line_out << "finish;";
    }
  }

  point->m_line_text = line_out.Base();

  // add entries for all non-temporary local variables of the function.

  const Vector<DefineVariable> *vars = mcfg->GetCFG()->GetVariables();

  if (vars) {
    for (size_t xind = 0; xind < vars->Size(); xind++) {
      const DefineVariable &def = vars->At(xind);

      if (def.var->Kind() != VK_Local &&
          def.var->Kind() != VK_Arg &&
          def.var->Kind() != VK_This)
        continue;

      if (!def.type->IsInt() && !def.type->IsFloat() &&
          !def.type->IsPointer())
        continue;

      // create a display value for the variable.
      Exp *lval = Exp::MakeVar(def.var);
      point->GetDisplayValue(lval, NULL);
    }
  }

  // get the baseline list of lvalues for checker frames in this stack frame.

  CheckerFrame *root_frame = chk_frame;
  while (CheckerFrame *parent_frame = root_frame->GetLoopParentFrame())
    root_frame = parent_frame;
  AddBaseLvalues(root_frame, point);

  // TODO: root_frame may still be a loop if we didn't set up the loop parent
  // relationships right. fix this.
  // Assert(root_frame->Kind() != B_Loop);

  // add entries for all lvalues used in the edge.
  Vector<Exp*> lval_list;
  LvalListVisitor visitor(&lval_list);
  if (edge)
    edge->DoVisit(&visitor);

  for (size_t lind = 0; lind < lval_list.Size(); lind++) {
    Exp *lval = lval_list[lind];

    // force creation of a display value for the lvalue.
    DisplayValue &lv = point->GetDisplayValue(lval, NULL);
    lv.m_force_display = true;
  }

  // find an edge which may have side effects at this point.

  const Vector<PEdge*> &outgoing =
    mcfg->GetCFG()->GetOutgoingEdges(cfg_point);

  PEdge *after_edge = NULL;

  if (outgoing.Size() == 1) {
    PEdge *edge = outgoing[0];
    if (edge->IsAssign() || edge->IsLoop() || edge->IsCall()) {
      after_edge = edge;

      // highlight edges which can GC when generating GC safety reports.
      if (chk_frame->State()->GetAssertKind() == ASK_GCSafe &&
          edge->IsCall() && chk_frame->Memory()->EdgeCanGC(edge)) {
        point->m_highlight = true;
      }
    }
  }

  const Vector<GuardAssign> *edge_assigns = mcfg->GetAssigns(cfg_point);

  if (edge_assigns)
    Assert(after_edge);

  // fill in values of all the lvalues we are listing at this point.

  for (size_t ind = 0; ind < point->m_values.Size(); ind++) {
    DisplayValue &lv = point->m_values[ind];

    // get the entry-relative exp the lvalue corresponds to.
    GuardExpVector lval_res;
    mcfg->TranslateExp(TRK_Point, cfg_point, lv.m_lval, &lval_res);
    lv.m_lval_use = solver->AsnChooseExp(solver_frame, lval_res);
    lv.m_rval = GetValString(chk_frame, cfg_point, lv, NULL);

    if (after_edge) {
      lv.m_newval = GetValString(chk_frame, cfg_point, lv, after_edge);

      // keep the value of the lvalue if either its string representation
      // changes across this edge or if it is explicitly assigned to.

      bool keep_value = false;
      if (edge_assigns) {
        for (size_t ind = 0; ind < edge_assigns->Size(); ind++) {
          const GuardAssign &gasn = edge_assigns->At(ind);
          if (gasn.left == lv.m_lval_use) {
            bool guard_value;
            solver->AsnBitValue(solver_frame, gasn.guard, &guard_value);

            if (guard_value)
              keep_value = true;
          }
        }
      }

      if (!keep_value && strcmp(lv.m_newval, lv.m_rval) == 0)
        lv.m_newval = NULL;
    }
  }

  // fill in argument information for calls.

  const Vector<GuardAssign> *arguments = mcfg->GetArguments(cfg_point);
  if (arguments) {
    for (size_t aind = 0; aind < arguments->Size(); aind++) {
      const GuardAssign &gts = arguments->At(aind);

      bool guard_value;
      solver->AsnBitValue(solver_frame, gts.guard, &guard_value);

      if (!guard_value)
        continue;

      DisplayValue value;
      value.m_lval = gts.left;

      Exp *rval_exp = gts.right;

      if (Type *type = rval_exp->GetType()) {
        value.m_bound_kind = BND_Offset;
        value.m_bound_type = type;
        rval_exp = Exp::MakeBound(BND_Offset, rval_exp, type);
      }

      value.m_rval = GetExpString(chk_frame, rval_exp);

      // add the new value to the list of lvalues at the point.
      point->m_values.PushBack(value);
    }
  }

  return point;
}

void DisplayPath::AddBaseLvalues(CheckerFrame *chk_frame, DisplayPoint *point)
{
  Vector<Exp*> terms;

  for (size_t pind = 0; pind < chk_frame->m_display_propagate.Size(); pind++) {
    CheckerPropagate *propagate = chk_frame->m_display_propagate[pind];

    for (size_t ind = 0; ind < propagate->m_point_terms.Size(); ind++) {
      Exp *exp = propagate->m_point_terms[ind];
      if (!terms.Contains(exp))
        terms.PushBack(exp);
    }
  }

  for (size_t ind = 0; ind < chk_frame->m_annotated_terms.Size(); ind++) {
    Exp *exp = chk_frame->m_annotated_terms[ind];
    if (!terms.Contains(exp))
      terms.PushBack(exp);
  }

  for (size_t ind = 0; ind < terms.Size(); ind++) {
    Exp *exp = terms[ind];

    DisplayMapper mapper;
    Exp *new_exp = exp->DoMap(&mapper);

    if (!new_exp) {
      // nothing we can do to display this in the UI. bail out.
      continue;
    }

    if (ExpDrf *nnew_exp = new_exp->IfDrf()) {
      DisplayValue &lv = point->GetDisplayValue(nnew_exp->GetTarget(), NULL);
      lv.m_force_display = true;
    }

    Exp *base = NULL;
    ExpBound *bound_kind = NULL;
    ExpTerminate *terminate_kind = NULL;

    GetExpBoundTerminate(new_exp, &base, &bound_kind, &terminate_kind);

    Exp *target = NULL;
    if (base && base->IsDrf())
      target = base->GetLvalTarget();

    if (target) {
      DisplayValue &lv = point->GetDisplayValue(target, NULL);
      lv.m_force_display = true;
    }

    if (target && bound_kind) {
      DisplayValue &bv = point->GetDisplayValue(target, NULL,
                                                bound_kind->GetBoundKind(),
                                                bound_kind->GetStrideType());
      bv.m_force_display = true;
    }

    if (terminate_kind) {
      DisplayValue &tv = point->GetDisplayValue(base, terminate_kind);
      tv.m_force_display = true;
    }
  }

  // also get information from any loop children.
  const Vector<PointFrameId> &callees = chk_frame->GetAllCallees();
  for (size_t ind = 0; ind < callees.Size(); ind++) {
    FrameId callee = callees[ind].id;
    if (CheckerFrame *callee_frame = chk_frame->State()->GetFrame(callee)) {
      if (callee_frame->Kind() == B_Loop)
        AddBaseLvalues(callee_frame, point);
    }
  }
}

const char* DisplayPath::GetValString(CheckerFrame *chk_frame,
                                      PPoint cfg_point,
                                      const DisplayValue &value,
                                      PEdge *after_edge)
{
  Assert(value.m_lval_use);

  Solver *solver = chk_frame->State()->GetSolver();
  BlockMemory *mcfg = chk_frame->Memory();

  // filtering for return lvalue whose initial value we don't care about.
  if (!after_edge) {
    if (ExpVar *nlval = value.m_lval_use->IfVar()) {
      if (nlval->GetVariable()->Kind() == VK_Return)
        return "*";
    }
  }

  // get the values to select the solver's assigned value from.
  GuardExpVector val_data;

  if (after_edge) {
    // get the values after the edge.
    Assert(after_edge->GetSource() == cfg_point);
    mcfg->TransferEdge(value.m_lval_use, value.m_kind, after_edge, &val_data);
  }
  else {
    // get the values before the edge.
    const Vector<GuardExp> &values =
      mcfg->GetVal(value.m_lval_use, value.m_kind, cfg_point);
    val_data.FillFromVector(values);
  }

  // get the particular value used by the solver's assignment.
  // there must be exactly one value.
  Exp *val_exp = solver->AsnChooseExp(chk_frame->Id(), val_data);

  // add an offset/bound if necessary.
  if (value.m_bound_type)
    val_exp = Exp::MakeBound(value.m_bound_kind, val_exp, value.m_bound_type);

  // get the string representation of the value.
  return GetExpString(chk_frame, val_exp);
}

const char* DisplayPath::GetExpString(CheckerFrame *chk_frame, Exp *exp)
{
  CheckerState *state = chk_frame->State();
  Solver *solver = state->GetSolver();

  BufferOutStream out(NewBuffer());

  mpz_t value;
  mpz_init(value);

  if (solver->AsnExpValue(chk_frame->Id(), exp, value))
    out << value;

  mpz_clear(value);

  if (out.m_buf->pos != out.m_buf->base)
    return out.Base();
  return "*";
}

NAMESPACE_XGILL_END
