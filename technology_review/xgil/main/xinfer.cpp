
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

#include <stdio.h>
#include <backend/backend_block.h>
#include <imlang/storage.h>
#include <memory/mstorage.h>
#include <infer/infer.h>
#include <infer/invariant.h>
#include <util/config.h>
#include <solve/solver.h>

NAMESPACE_XGILL_USING

const char *USAGE = "xinfer [options] [function*]";

// currently, xinfer is not entirely deterministic. this is not a big problem,
// there isn't much cross-function dependency here (unlike xmemlocal).
// there are two issues:
// 1. after finishing a stage, analysis does not wait for all summaries for
// that stage to come in before starting the next stage. we can't use the
// same barriers as in xmemlocal as we want to be tolerant of crashes/failures.
// 2. analysis of functions in the last stage may use the summaries computed
// earlier for other functions in that stage.

// counter indicating the index of the *next* pass we'll be processing.
#define COUNTER_STAGE "counter"

// number of callgraph stages.
static size_t g_stage_count = 0;

// perform an initialization transaction to setup the callgraph/worklist.
void DoInitTransaction(Transaction *t, const Vector<const char*> &functions)
{
  // this is the same as for memory/modset computation, load/seed the worklist.

  size_t count_var = t->MakeVariable(true);

  if (!functions.Empty()) {
    TOperandList *new_functions = new TOperandList(t);
    for (size_t ind = 0; ind < functions.Size(); ind++)
      new_functions->PushOperand(new TOperandString(t, functions[ind]));

    t->PushAction(Backend::BlockSeedWorklist(t, new_functions));
  }
  else {
    t->PushAction(Backend::BlockLoadWorklist(t, count_var));
  }

  SubmitTransaction(t);

  if (functions.Empty())
    g_stage_count = t->LookupInteger(count_var)->GetValue();
}

// perform a transaction to get the next key from the worklist. the body data
// will not be set if no key was fetched.
void DoFetchTransaction(Transaction *t, size_t stage_result,
                        size_t body_data_result,
                        size_t memory_data_result, size_t modset_data_result)
{
  TRANSACTION_MAKE_VAR(body_key);
  TRANSACTION_MAKE_VAR(key_empty);

  t->PushAction(Backend::BlockCurrentStage(t, stage_result));
  t->PushAction(Backend::BlockPopWorklist(t, body_key_var));
  t->PushAction(Backend::StringIsEmpty(t, body_key, key_empty_var));

  TActionTest *non_empty_branch = new TActionTest(t, key_empty, false);
  t->PushAction(non_empty_branch);

  non_empty_branch->PushAction(
    Backend::XdbLookup(t, BODY_DATABASE, body_key, body_data_result));
  non_empty_branch->PushAction(
    Backend::XdbLookup(t, MEMORY_DATABASE, body_key, memory_data_result));
  non_empty_branch->PushAction(
    Backend::XdbLookup(t, MODSET_DATABASE, body_key, modset_data_result));

  SubmitTransaction(t);
}

ConfigOption print_cfgs(CK_Flag, "print-cfgs", NULL,
                        "print input CFGs");

ConfigOption print_memory(CK_Flag, "print-memory", NULL,
                          "print input memory information");

// how often to print allocation/timer information.
#define PRINT_FREQUENCY 50
size_t g_print_counter = 0;

void RunAnalysis(const Vector<const char*> &functions)
{
  static BaseTimer analysis_timer("xinfer_main");
  Transaction *t = new Transaction();

  // we will manually manage clearing of entries in the summary cache.
  BlockSummaryCache.SetLruEviction(false);

  DoInitTransaction(t, functions);
  t->Clear();

  // current stage being processed.
  size_t current_stage = 0;

  while (true) {
    Timer _timer(&analysis_timer);
    ResetTimeout();

    g_print_counter++;

    if (g_print_counter % PRINT_FREQUENCY == 0) {
      PrintTimers();
      PrintAllocs();
    }

    size_t stage_result = t->MakeVariable(true);
    size_t body_data_result = t->MakeVariable(true);
    size_t memory_data_result = t->MakeVariable(true);
    size_t modset_data_result = t->MakeVariable(true);

    DoFetchTransaction(t, stage_result, body_data_result,
                       memory_data_result, modset_data_result);

    size_t new_stage = t->LookupInteger(stage_result)->GetValue();

    if (new_stage > current_stage) {
      if (new_stage > g_stage_count) {
        // we've generated summaries for every function. end the analysis.
        break;
      }
      current_stage = new_stage;
    }

    if (!t->Lookup(body_data_result, false)) {
      // the current stage is finished, and the transaction bumped the stage
      // counter. retry, we'll get any item from the new stage.
      t->Clear();
      continue;
    }

    Vector<BlockCFG*> block_cfgs;
    BlockCFGUncompress(t, body_data_result, &block_cfgs);
    Assert(!block_cfgs.Empty());

    Vector<BlockMemory*> block_mems;
    BlockMemoryUncompress(t, memory_data_result, &block_mems);
    BlockMemoryCacheAddList(block_mems);

    Vector<BlockModset*> block_mods;
    TOperandString *modset_op = t->LookupString(modset_data_result);
    BlockModsetUncompress(t, modset_op, &block_mods);
    BlockModsetCacheAddList(block_mods);

    t->Clear();

    // generate summaries.

    String *function = block_cfgs[0]->GetId()->Function();
    logout << "Generating summaries for "
           << "\'" << function->Value() << "\'" << endl << flush;

    // generate summaries for each of the CFGs.
    Vector<BlockSummary*> block_sums;

    for (size_t find = 0; find < block_cfgs.Size(); find++) {
      BlockCFG *cfg = block_cfgs[find];
      BlockId *id = cfg->GetId();

      BlockMemory *mcfg = GetBlockMemory(id);

      if (mcfg == NULL) {
        logout << "WARNING: Missing memory: " << id << endl;
        continue;
      }

      if (print_cfgs.IsSpecified())
        logout << cfg << endl;

      if (print_memory.IsSpecified())
        logout << mcfg << endl;

      BlockSummary *sum = BlockSummary::Make(id);
      sum->SetMemory(mcfg);

      block_sums.PushBack(sum);
    }

    // make sure the cache knows about these summaries.
    BlockSummaryCacheAddList(block_sums);

    InferSummaries(block_sums);

    // print the summaries to screen.
    for (size_t find = 0; find < block_sums.Size(); find++) {
      BlockSummary *sum = block_sums[find];
        logout << "Computed summary:" << endl << sum << endl;
    }

    logout << "Elapsed: ";
    PrintTime(_timer.Elapsed());
    logout << endl << endl;

    TOperand *body_key = new TOperandString(t, function->Value());
    TOperand *summary_data_arg = BlockSummaryCompress(t, block_sums);
    t->PushAction(Backend::XdbReplace(t, SUMMARY_DATABASE,
                                      body_key, summary_data_arg));
    SubmitTransaction(t);
    t->Clear();
  }

  delete t;
}

int main(int argc, const char **argv)
{
  timeout.Enable();
  trans_remote.Enable();
  trans_initial.Enable();

  solver_use.Enable();
  solver_verbose.Enable();
  solver_constraint.Enable();

  print_invariants.Enable();
  print_cfgs.Enable();
  print_memory.Enable();

  Vector<const char*> functions;
  bool parsed = Config::Parse(argc, argv, &functions);
  if (!parsed) {
    Config::PrintUsage(USAGE);
    return 1;
  }

  // Solver::CheckSimplifications();

  ResetAllocs();
  AnalysisPrepare();

  if (trans_initial.IsSpecified())
    SubmitInitialTransaction();
  RunAnalysis(functions);
  SubmitFinalTransaction();

  ClearBlockCaches();
  ClearMemoryCaches();
  AnalysisFinish(0);
}
