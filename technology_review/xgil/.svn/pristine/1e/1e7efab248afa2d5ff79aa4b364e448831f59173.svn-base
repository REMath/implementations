
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

#include <memory/mblock.h>  

// management of propagation decision points.

NAMESPACE_XGILL_BEGIN

// the checker will attempt an exhaustive enumeration of the program's
// possible behaviors when trying to prove an assertion. while the order
// it performs this enumeration could affect whether it finds a report
// rather than an incomplete, this order will not affect whether it is able
// to check the assertion successfully. however, there are points during
// its execution where it can make a decision about *how* to try to prove
// the property. once made these decisions cannot be undone, and the decision
// made often determines whether the checker will quickly prove the assertion,
// or just spin off and give back incomplete.

// since the checker is deterministic, we can model the possible decisions
// it could make during its execution with a binary tree whose children
// represent the decisions that will be made if it decides yes/no at
// a particular point. during checking, we will perform a breadth-first search
// of the nodes in this decision tree, until we check the assertion holds,
// get a report or run out of time.

// unique identifier for decisions. as with checker frames, these can
// be used by decision points to refer to one another. 0 refers to
// a non-existent decision point.
typedef size_t DecisionId;

// kinds of nodes in the decision tree. leaves in the tree are either
// unexplored or incomplete.
enum CheckerDecisionKind {
  // unexplored point in the decision tree.
  CDK_Unexplored,

  // decision points in the tree which will lead to an incomplete.
  CDK_Incomplete,

  // whether to use a specific sufficient condition.
  CDK_Sufficient,

  // whether to perform eager propagation on a specific type.
  CDK_Invariant
};

inline const char* DecisionKindString(CheckerDecisionKind kind)
{
  switch (kind) {
  case CDK_Unexplored:  return "Unexplored";
  case CDK_Incomplete:  return "Incomplete";
  case CDK_Sufficient:  return "Sufficient";
  case CDK_Invariant:   return "Invariant";
  default:
    Assert(false);
    return NULL;
  }
}

// decision tree nodes, representing either a decision point with a yes/no
// answer, or an unexplored/incomplete leaf.
struct CheckerDecision
{
  // unique ID of this decision.
  DecisionId m_id;

  // kind of decision this is.
  CheckerDecisionKind m_kind;

  // decision we will make next if we answer this decision in the affirmative
  // or negative. the checker behaves deterministically so we only need
  // a single yes and no child. only used for non-leaf nodes.
  DecisionId m_child_yes;
  DecisionId m_child_no;

  // CDK_Sufficient data: the block where the sufficient condition was found,
  // and the sufficient condition which we are deciding on.
  BlockId *m_sufficient_block;
  Bit *m_sufficient_bit;

  // CDK_Invariant data: the type to perform eager propagation on.
  String *m_invariant_csu;

  CheckerDecision(DecisionId id)
    : m_id(id), m_kind(CDK_Unexplored),
      m_sufficient_block(NULL), m_sufficient_bit(NULL),
      m_invariant_csu(NULL)
  {}

  void Print()
  {
    logout << "Decision " << m_id << ": " << DecisionKindString(m_kind)
           << " [" << m_child_yes << ", " << m_child_no << "]" << endl;

    if (m_sufficient_block)
      logout << "  sufficient_block " << m_sufficient_block << endl;
    if (m_sufficient_bit)
      logout << "  sufficient_bit " << m_sufficient_bit << endl;

    if (m_invariant_csu)
      logout << "  invariant_csu " << m_invariant_csu << endl;
  }
};

// explored portion of the decision tree. this is initially a single empty
// node, and will grow as possible checker decisions are found. the intention
// is that the checker should have to make relatively few decisions and that
// this tree stays small and amenable to reasonably exhaustive exploration.
struct CheckerDecisionTree
{
  // all nodes in the decision tree.
  Vector<CheckerDecision*> m_decisions;

  // the root of the decision tree. this is the first decision found when
  // the checker starts running as with the decision child case, the checker
  // is deterministic so the first encountered decision is always the same.
  // if the checker has not started running at all this will be zero,
  // and if the checker has started but there are no decisions yet this
  // will be a decision with CDK_Empty.
  DecisionId m_root_id;

  // number of unexplored nodes in the decision tree. when this goes to zero
  // we have exhaustively searched the tree.
  size_t m_unexplored_count;

  // gets a new decision and adds it to this table.
  CheckerDecision* MakeDecision()
  {
    size_t id = m_decisions.Size();
    CheckerDecision *decision = new CheckerDecision(id);

    m_decisions.PushBack(decision);
    return decision;
  }

  // gets an existing decision with the specified ID.
  CheckerDecision* GetDecision(DecisionId id)
  {
    CheckerDecision *decision = m_decisions[id];
    Assert(decision);
    return decision;
  }

  // prints the entire tree to stdout.
  void Print()
  {
    logout << "Decision Tree:" << endl;
    for (size_t ind = 0; ind < m_decisions.Size(); ind++) {
      if (m_decisions[ind])
        m_decisions[ind]->Print();
    }
  }

  // current path data.

  // path in the decision tree taken by the current checker exploration.
  // this is a chain of yes/no answers to follow from the root.
  // does not describe the entire path --- the last node in the
  // path will be an Empty node, and once we start exploring this space
  // all further decisions are 'yes'.
  Vector<bool> m_path;

  // checker's index into the decision path. this will equal the size of
  // m_path if we have run over and into unexplored parts of the tree.
  size_t m_path_position;

  // ID of the checker's next decision. this will be a CDK_Empty if we
  // are in unexplored parts of the tree, a non-leaf decision node otherwise.
  DecisionId m_path_decision;

  // set the checker path to the next path in the breadth first exploration
  // of this decision tree. returns true on success, false on exhaustive
  // enumeration of the decision tree.
  bool NextPath();

  // constructors.

  CheckerDecisionTree()
  {
    m_decisions.PushBack(NULL);

    // make an unexplored decision point at the root.
    CheckerDecision *root_decision = MakeDecision();
    m_root_id = root_decision->m_id;
    m_unexplored_count = 1;

    // set up the initial checker path.
    m_path_position = 0;
    m_path_decision = m_root_id;
  }

  ~CheckerDecisionTree()
  {
    for (size_t ind = 0; ind < m_decisions.Size(); ind++) {
      if (m_decisions[ind])
        delete m_decisions[ind];
    }
  }
};

NAMESPACE_XGILL_END
