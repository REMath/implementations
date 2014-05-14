
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

#include "clobber.h"
#include "mblock.h"
#include "mstorage.h"

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// MemoryClobber static
/////////////////////////////////////////////////////////////////////

// list of all MemoryClobber structures, indexed by their kind.
static Vector<MemoryClobber*> *g_clobber_list = NULL;

MemoryClobber* MemoryClobber::Lookup(MemoryClobberKind kind)
{
  Assert(g_clobber_list != NULL);

  size_t ind = (size_t) kind;
  Assert(ind < g_clobber_list->Size());
  Assert(g_clobber_list->At(ind) != NULL);

  return g_clobber_list->At(ind);
}

void MemoryClobber::Register(MemoryClobber *clobber)
{
  // this is called during static initialization so make sure
  // g_clobber_list is setup properly.
  static bool initialized_clobber_list = false;
  if (!initialized_clobber_list) {
    g_clobber_list = new Vector<MemoryClobber*>();
    initialized_clobber_list = true;
  }

  size_t ind = (size_t) clobber->m_kind;
  while (ind >= g_clobber_list->Size())
    g_clobber_list->PushBack(NULL);

  Assert(g_clobber_list->At(ind) == NULL);
  g_clobber_list->At(ind) = clobber;
}

MemoryClobber mclobber_Default(MCLB_Default);

/////////////////////////////////////////////////////////////////////
// MemoryClobberModset
/////////////////////////////////////////////////////////////////////

class MemoryClobberModset : public MemoryClobber
{
 public:
  bool m_indirect;
  MemoryClobberModset(bool indirect)
    : MemoryClobber(indirect ? MCLB_Modset : MCLB_ModsetNoIndirect),
      m_indirect(indirect) {}

  void ComputeClobberCall(BlockMemory *mcfg, PEdge *edge,
                          Vector<GuardAssign> *assigns,
                          Vector<GuardAssign> *clobbered,
                          bool direct, BlockId *callee, Exp *rfld_chain)
  {
    PPoint point = edge->GetSource();
    BlockModset *modset = GetBlockModset(callee);

    // fill the assigns in the caller, but only for direct calls.
    if (direct) {
      for (size_t ind = 0; ind < modset->GetAssignCount(); ind++) {
        const GuardAssign &gts = modset->GetAssign(ind);
        mcfg->TranslateAssign(TRK_Callee, point, NULL,
                              gts.left, gts.right, gts.guard, assigns);
      }
    }

    for (size_t mind = 0; mind < modset->GetModsetCount(); mind++) {
      const PointValue &cv = modset->GetModsetLval(mind);
      Exp *new_lval = CallEdgeAddRfldExp(cv.lval, callee, rfld_chain);

      GuardExpVector caller_res;
      mcfg->TranslateExp(TRK_Callee, point, new_lval, &caller_res);

      for (size_t ind = 0; ind < caller_res.Size(); ind++) {
        const GuardExp &gt = caller_res[ind];

        // filter out lvalues containing rfld.
        if (gt.exp->RfldCount() > 0)
          continue;

        GuardAssign gti(gt.exp, cv.lval, gt.guard, cv.kind);
        clobbered->PushBack(gti);
      }
    }
  }

  void ComputeClobber(BlockMemory *mcfg, PEdge *edge,
                      Vector<GuardAssign> *assigns,
                      Vector<GuardAssign> *clobbered)
  {
    // only clobbering values written by direct calls and loops.
    PPoint point = edge->GetSource();

    if (BlockId *callee = edge->GetDirectCallee()) {
      ComputeClobberCall(mcfg, edge, assigns, clobbered,
                         true, callee, NULL);
    }
    else if (edge->IsCall() && m_indirect) {
      Variable *function = mcfg->GetId()->BaseVar();
      CallEdgeSet *indirect_callees = CalleeCache.Lookup(function);

      if (indirect_callees) {
        for (size_t ind = 0; ind < indirect_callees->GetEdgeCount(); ind++) {
          const CallEdge &cedge = indirect_callees->GetEdge(ind);

          if (cedge.where.version == mcfg->GetCFG()->GetVersion() &&
              cedge.where.id == mcfg->GetId() &&
              cedge.where.point == point) {
            BlockId *callee = BlockId::Make(B_Function, cedge.callee);

            ComputeClobberCall(mcfg, edge, assigns, clobbered,
                               false, callee, cedge.rfld_chain);
          }
        }
      }

      CalleeCache.Release(function);
    }
  }
};

MemoryClobberModset msimp_Modset(true);
MemoryClobberModset msimp_ModsetNoIndirect(false);

NAMESPACE_XGILL_END
