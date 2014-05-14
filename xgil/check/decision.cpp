
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

#include "decision.h"

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// CheckerDecisionPath
/////////////////////////////////////////////////////////////////////

bool CheckerDecisionTree::NextPath()
{
  m_path_position = 0;
  m_path_decision = m_root_id;

  if (m_unexplored_count == 0) {
    m_path.Clear();
    return false;
  }

  // the checker decision paths are binary strings of yes/no,
  // where the first entries in the path are the first decisions made.
  // treat the path as a binary number with 'yes' as 0, 'no' as 1,
  // and with the first entries in the path the least significant bits.
  // then we can get a breadth first search by repeatedly 'incrementing'
  // the path, which will explore the 'no' answers for the earliest
  // decisions the most frequently in relation to 'no' answers for
  // later decisions.

  // we will keep incrementing until we hit an unexplored part of the tree.
  // there is no sense exploring a path we know will give back incomplete.
  while (true) {

    size_t ind = 0;
    while (ind < m_path.Size() && !m_path[ind]) {
      m_path[ind] = true;
      ind++;
    }

    if (ind == m_path.Size())
      m_path.PushBack(false);
    else
      m_path[ind] = false;

    // check to see if this path is known to go to incomplete.
    bool is_incomplete = false;

    CheckerDecision *cur = GetDecision(m_root_id);
    for (size_t pos = 0; pos < m_path.Size(); pos++) {
      DecisionId next_id = m_path[pos] ? cur->m_child_yes : cur->m_child_no;
      if (next_id == 0) {
        Assert(cur->m_kind == CDK_Incomplete);
        is_incomplete = true;
        break;
      }

      cur = GetDecision(next_id);
    }

    if (!is_incomplete) {
      Assert(cur->m_kind == CDK_Unexplored);
      break;
    }
  }

  return true;
}

NAMESPACE_XGILL_END
