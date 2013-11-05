
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

// propagation rule interface for checker search.

#include "checker.h"
#include "where.h"

NAMESPACE_XGILL_BEGIN

// propagation control structure. describes the actions that should be taken
// by the checker at each point during the checker's exploration DFS.
// these are stack allocated by the checker.
struct CheckerPropagate
{
  // CheckerPropagate fields.

  // checker frame this is performing propagation for.
  CheckerFrame *m_frame;

  // unique identifier for this propagation in the checker state.
  size_t m_id;

  // point within the frame this propagation is working backwards from.
  // this is the same as the frame->m_point unless we are visiting the same
  // frame multiple times with different propagations.
  PPoint m_point;

  // whether side effects from calls/loops at point can be included
  // in the safe bit. (side effects from later points are never included).
  bool m_allow_point;

  // whether to prefer preconditions over invariants for a given bit.
  bool m_prefer_precondition;

  // description of the action the checker should take.
  Where *m_where;

  // asserted bit we started with, which was asserted at m_point.
  Bit *m_base_bit;

  // the asserted bit converted at m_point. this is the bit we generate
  // m_where from, and might be different from the bit in m_where.
  Bit *m_point_bit;

  // list of terms in m_point_bit.
  Vector<Exp*> m_point_terms;

  // all bits we have tested for sufficient conditions.
  Vector<Bit*> m_sufficient_tested_list;

  // subset of tested_list which generally fit the criteria for sufficient
  // conditions, but which might not ensure the assert holds.
  Vector<Bit*> m_sufficient_possible_list;

  // subset of possible_list which actually are sufficient conditions.
  Vector<Bit*> m_sufficient_list;

  // CheckerPropagate methods.

  CheckerPropagate(CheckerFrame *frame, PPoint point, bool allow_point);
  ~CheckerPropagate();

  // can't assign or copy propagations.
  CheckerPropagate(CheckerPropagate&) { Assert(false); }
  CheckerPropagate& operator = (const CheckerPropagate&) { Assert(false); }

  // fill this propagation in based on the specified point bit, using either
  // the point bit itself as the propagation bit, or a weakened sufficient
  // condition for the point bit.
  void FindTest(Bit *base_bit, Bit *point_bit);

  // set m_where according to the terms in safe_bit.
  void SetTest(Bit *safe_bit);

  // helper to set the bit this propagate was derived from.
  void SetBaseBit(Bit *base_bit, Bit *point_bit);

  // helper for SetTest, try to make a direction for the specified lvalue
  // appearing in the safe bit.
  Where* TryPropagate(Bit *bit, Exp *lval);

  // print debug information on this propagation to stdout.
  void Print();
};

NAMESPACE_XGILL_END
