
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

#pragma once

// construction and emission of user-displayable path information.

#include <memory/summary.h>

NAMESPACE_XGILL_BEGIN

// forward declarations.
struct CheckerState;
struct CheckerFrame;
class Where;

// XML format of paths:

// path:  name frame+ point+ frameindex+
// frame: frameindex beginpoint endpoint text file beginline endline
//        maintext wheretext framechild? framenext? annotation* hook+
// point: pointindex line linetext highlight? value*
// value: lval rval newval?
// hook: text name+

// string tags:
//   text name file maintext wheretext annotation linetext lval rval newval
// integer tags:
//   frameindex beginpoint endpoint framechild framenext pointindex line
//   beginline endline

// forward declarations.
struct DisplayPoint;
struct DisplayFrame;
struct DisplayPath;

// stores the value held by a particular lvalue at some point in the path.
struct DisplayValue
{
  DisplayValue();

  // lval and value kind. the lvalue is in terms of the state at the point.
  Exp *m_lval;
  Exp *m_kind;

  // the entry-relative lvalue which lval corresponds to at the point.
  Exp *m_lval_use;

  // text for the value of this lval. points into a buffer in the outer
  // DisplayPath or which outlives the DisplayPath. '*' for don't care values.
  const char *m_rval;

  // text for the value of this lval after the edge following the
  // containing point. NULL if the lval is not written by the edge.
  // ditto otherwise with m_rval.
  const char *m_newval;

  // whether the rval/newval values represent a buffer offset/bound on the
  // lvalue, or just a scalar value.
  BoundKind m_bound_kind;
  Type *m_bound_type;

  // force display of this value, even if it is a don't-care.
  bool m_force_display;

  // write a <value> tag for this to the specified buffer.
  void WriteXML(Buffer *buf);
};

// stores all information held about a particular point in the path.
struct DisplayPoint
{
  DisplayPoint();

  // index of this point in the generated path.
  size_t m_index;

  // call frame in which this point occurs.
  DisplayFrame *m_frame;

  // point in the frame's CFG this corresponds to.
  PPoint m_cfg_point;

  // text to display when browsing to this point in the frame.
  const char *m_line_text;

  // whether to highlight this point in the generated path.
  bool m_highlight;

  // list of values to display at this point.
  Vector<DisplayValue> m_values;

  // get the display value for lval, or make a new one if one does not exist.
  DisplayValue& GetDisplayValue(Exp *lval, Exp *kind,
                                BoundKind bound_kind = BND_Invalid,
                                Type *bound_type = NULL);

  // write a <point> tag for this to the specified buffer.
  void WriteXML(Buffer *buf);
};

// stores information about a hook where one can add annotations
// from within the UI.
struct AnnotationHook
{
  AnnotationHook() : m_text(NULL), m_name(NULL) {}

  // description of this hook.
  const char *m_text;

  // name of the annotation function to use with the hook.
  // as with Where::PrintHook, the '$' character is used as a separator if
  // there are multiple annotation functions.
  const char *m_name;
};

// a contiguous section of the path in one CFG block. these are one to one
// with checker propagations: each checker frame has at least one display
// frame, and has more than one if that checker frame has multiple callees.
struct DisplayFrame
{
  DisplayFrame();

  // index of this frame in the generated path.
  size_t m_index;

  // CFG used by all points in this frame.
  BlockCFG *m_cfg;

  // indexes of the begin and end points in this frame. the points in the
  // frame are the contiguous sequence between these.
  size_t m_begin_point;
  size_t m_end_point;

  // text for the assertion driving analysis for this frame.
  const char *m_main_text;

  // text for the propagation performed from the assertion.
  const char *m_where_text;

  // index of any callee of this frame.
  size_t m_callee_frame;

  // index of the frame which the path returns to after m_callee_frame,
  // if there is one. may be specified without m_callee_frame for
  // skipped loops.
  size_t m_next_frame;

  // text for any annotations consumed within this frame.
  Vector<const char*> m_annotations;

  // the kinds of annotations that can be added for this frame.
  Vector<AnnotationHook> m_annotation_hooks;

  // types and variables we have emitted invariant hooks for, to avoid dupes.
  Vector<TypeCSU*> m_type_hooks;
  Vector<Variable*> m_global_hooks;

  // write a <frame> tag for this to the specified buffer.
  void WriteXML(Buffer *buf);
};

// a partial or complete path visiting one or more call frames in the program.
struct DisplayPath
{
  DisplayPath();
  ~DisplayPath();

  // write a <path> tag for this to the specified buffer.
  void WriteXML(Buffer *buf);

  // makes and appends to this path a display frame for chk_frame starting
  // at point. also makes and adds to the path any transitive callees or
  // heap successors of chk_frame. threads added points onto m_end_point.
  DisplayFrame* MakeFrame(CheckerFrame *chk_frame, PPoint cfg_point);

  // adds a hook for the direction indicated by the (empty) where to frame.
  void AddHook(DisplayFrame *frame, Where *where);

  // adds any annotations from assume_list matching point to frame.
  void AddAnnotations(DisplayFrame *frame,
                      const Vector<AssumeInfo> &assume_list,
                      PPoint point, PEdge *edge);

  // makes and appends to this path a display point for cfg_point
  // in chk_frame.
  DisplayPoint* MakePoint(CheckerFrame *chk_frame, PPoint cfg_point);

  // helper methods.

  // add to point all base lvalues for chk_frame and its outer function.
  // this is all lvalues mentioned in the propagations or assumptions of
  // the checker frame for the outer function and any inner loops.
  void AddBaseLvalues(CheckerFrame *chk_frame, DisplayPoint *point);

  // gets the string representation for the specified expression in chk_frame,
  // or NULL for don't-care expressions.
  const char* GetExpString(CheckerFrame *chk_frame, Exp *exp);

  // gets the string representation for the value of lval per kind
  // at cfg_point within chk_frame, according to GetExpString. if after_edge
  // is set then the value will reflect any side effects at cfg_point.
  const char* GetValString(CheckerFrame *chk_frame,
                           PPoint cfg_point, const DisplayValue &value,
                           PEdge *after_edge);

  // fills the out stream in with the printable name for an lvalue.
  void GetPrintName(CheckerFrame *chk_frame, Exp *lval, BufferOutStream &out);

  // get a fresh buffer for data referenced by this path.
  Buffer* NewBuffer() {
    Buffer *buf = new Buffer(100);
    m_buffers.PushBack(buf);
    return buf;
  }

  // instance values.

  // whether XML for this path has been emitted. this can be done at most once
  // and afterward the path can only be deleted.
  bool m_emitted_xml;

  // name of this path, if available.
  const char *m_name;

  // the different frames visited by this path, in order of execution.
  Vector<DisplayFrame*> m_frames;

  // the different points in this path, in order of execution.
  Vector<DisplayPoint*> m_points;

  // indexes of all root frames in this path, not sorted.
  Vector<size_t> m_frame_roots;

  // the buffers owned by this path which will be deleted when the path
  // is destroyed.
  Vector<Buffer*> m_buffers;
};

NAMESPACE_XGILL_END
