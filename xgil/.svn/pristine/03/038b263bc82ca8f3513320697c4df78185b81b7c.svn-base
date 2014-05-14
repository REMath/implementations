
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
#include <unistd.h>
#include <sys/resource.h>

#include <imlang/block.h>
#include <imlang/storage.h>
#include <memory/mblock.h>
#include <memory/escape.h>
#include <memory/mstorage.h>
#include <backend/backend_block.h>
#include <backend/backend_compound.h>
#include <util/config.h>
#include <util/monitor.h>
#include <solve/solver.h>

NAMESPACE_XGILL_USING

const char *USAGE = "xmemlocal [options] [function*]";

// the memory model for a function is entirely determined from its CFG
// and from the modsets of its callees. getting complete modsets is an
// iterative process due to recursion, and we want to make this iteration
// deterministic. the process for computing memory and modsets is as follows:
//
// 1. compute the memory/modsets for all but the last stage of the callgraph.
// 2. run one pass over the last stage of the callgraph to compute modset
// dependencies and the first cut of the modsets for these functions.
// 3. run additional passes over the last stage of the callgraph.
// maintain a worklist of the functions to analyze in the next pass
// (any function with a callee whose modset changed in the current pass).

// new memory or modset data is not written to the databases until a pass
// is finished. the next pass does not start until after this writing is done.
// this is managed using a barrier counter, which indicates the number of
// outstanding workers for the current pass which have made new memory/modset
// data but have not written it out yet.

// hash name for the modset dependency information (if it is being generated).
#define MODSET_DEPENDENCY_HASH "dependency_modset"

// scratch buffer for database compression.
static Buffer compress_buf("Buffer_xmemlocal");

ConfigOption pass_limit(CK_UInt, "pass-limit", "0",
                        "maximum number of passes to perform, 0 for no limit");

ConfigOption print_cfgs(CK_Flag, "print-cfgs", NULL,
                        "print input CFGs");

ConfigOption print_memory(CK_Flag, "print-memory", NULL,
                          "print generated memory information");

// number of callgraph stages.
static size_t g_stage_count = 0;

// number of stages we will actually analyze, zero for no limit (fixpointing).
static size_t g_stage_limit = 0;

// perform an initialization transaction to setup the callgraph/worklist.
void DoInitTransaction(Transaction *t, const Vector<const char*> &functions)
{
  // either load the worklist from file or seed it with the functions
  // we got from the command line.

  size_t count_var = t->MakeVariable(true);

  if (!functions.Empty()) {
    TOperandList *new_functions = new TOperandList(t);
    for (size_t ind = 0; ind < functions.Size(); ind++)
      new_functions->PushOperand(new TOperandString(t, functions[ind]));

    t->PushAction(Backend::BlockSeedWorklist(t, new_functions));

    // don't fixpoint analysis if we are running on command line functions.
    g_stage_limit = 1;
  }
  else {
    t->PushAction(Backend::BlockLoadWorklist(t, count_var));
  }

  SubmitTransaction(t);

  if (functions.Empty()) {
    // get the stage count and set the pass limit.
    g_stage_count = t->LookupInteger(count_var)->GetValue();

    if (pass_limit.UIntValue() != 0)
      g_stage_limit = g_stage_count + pass_limit.UIntValue();
  }
}

// perform a transaction to get the next key from the worklist. the body data
// will not be set if there are no nodes remaining in the worklist.
// have_process indicates whether we have a count on the process barrier,
// process_result and write_result receives whether any worker has a count
// on those barriers.
void DoFetchTransaction(Transaction *t, size_t stage_result,
                        size_t body_data_result, size_t modset_data_result)
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
    Backend::XdbLookup(t, MODSET_DATABASE, body_key, modset_data_result));

  SubmitTransaction(t);
}

// get a list of all the direct and indirect callees of this function,
// and do a batch load of all modsets for these callees.
void GetCalleeModsets(Transaction *t,
                      const Vector<BlockCFG*> &block_cfgs, size_t stage,
                      Vector<Variable*> *callees)
{
  Variable *function = block_cfgs[0]->GetId()->BaseVar();

  // process direct calls.
  for (size_t ind = 0; ind < block_cfgs.Size(); ind++) {
    BlockCFG *cfg = block_cfgs[ind];
    for (size_t eind = 0; eind < cfg->GetEdgeCount(); eind++) {
      if (PEdgeCall *edge = cfg->GetEdge(eind)->IfCall()) {
        Variable *callee = edge->GetDirectFunction();
        if (callee && !callees->Contains(callee))
          callees->PushBack(callee);
      }
    }
  }

  // process indirect calls. how this works depends on the stage.
  if (stage < g_stage_count) {
    // there are no indirect calls in this function.
  }
  else if (stage == g_stage_count) {
    // there may be indirect calls, and this is the first time this function
    // has been processed. compute the targets, and store in the merge
    // list to write out when this stage finishes.
    for (size_t ind = 0; ind < block_cfgs.Size(); ind++)
      CallgraphProcessCFGIndirect(block_cfgs[ind], callees);
  }
  else {
    // we already know the indirect targets of this function, get them
    // from the callgraph.
    CallEdgeSet *cset = CalleeCache.Lookup(function);
    for (size_t ind = 0; cset && ind < cset->GetEdgeCount(); ind++) {
      Variable *callee = cset->GetEdge(ind).callee;
      if (!callees->Contains(callee))
        callees->PushBack(callee);
    }
    CalleeCache.Release(function);
  }

  // fetch the callee modsets as a single transaction.
  size_t modset_list_result = t->MakeVariable(true);
  TOperand *modset_list_arg = new TOperandVariable(t, modset_list_result);

  TRANSACTION_MAKE_VAR(modset_data);

  Vector<TOperand*> empty_list_args;
  t->PushAction(Backend::ListCreate(t, empty_list_args, modset_list_result));

  for (size_t find = 0; find < callees->Size(); find++) {
    Variable *callee = callees->At(find);
    TOperand *callee_arg = new TOperandString(t, callee->GetName()->Value());

    // don't get the modset if it is already cached.
    BlockId *id = BlockId::Make(B_Function, callee);

    if (!BlockModsetCache.IsMember(id)) {
      t->PushAction(Backend::XdbLookup(t, MODSET_DATABASE,
                                       callee_arg, modset_data_var));
      t->PushAction(Backend::ListPush(t, modset_list_arg, modset_data,
                                      modset_list_result));
    }
  }

  SubmitTransaction(t);

  // add the fetched modsets to the modset cache.
  TOperandList *modset_list = t->LookupList(modset_list_result);
  for (size_t oind = 0; oind < modset_list->GetCount(); oind++) {
    TOperandString *modset_data = modset_list->GetOperand(oind)->AsString();

    Vector<BlockModset*> bmod_list;
    BlockModsetUncompress(t, modset_data, &bmod_list);
    BlockModsetCacheAddList(bmod_list);
  }

  t->Clear();
}

// generate the memory and modset information for the specified CFGs.
// return whether the generation was successful (no timeout).
bool GenerateMemory(const Vector<BlockCFG*> &block_cfgs, size_t stage,
                    Vector<BlockMemory*> *block_mems,
                    Vector<BlockModset*> *block_mods)
{
  Variable *function = block_cfgs[0]->GetId()->BaseVar();

  // did we have a timeout while processing the CFGs?
  bool had_timeout = false;

  // generate memory information and (possibly) modsets for each CFG.
  for (size_t cind = 0; cind < block_cfgs.Size(); cind++) {
    // set a soft timeout for memory/modset computation.
    // we don't set a hard timeout as these break the indirect callgraph.
    if (uint32_t timeout = GetTimeout())
      TimerAlarm::StartActive(timeout);

    BlockCFG *cfg = block_cfgs[cind];
    BlockId *id = cfg->GetId();

    if (print_cfgs.IsSpecified())
      logout << cfg << endl;

    bool indirect = (stage > g_stage_count);

    MemoryClobberKind clobber_kind =
      indirect ? MCLB_Modset : MCLB_ModsetNoIndirect;

    BlockMemory *mem =
      BlockMemory::Make(id, MSIMP_Scalar, MALIAS_Buffer, clobber_kind);

    mem->SetCFG(cfg);
    mem->ComputeTables();

    String *loop = id->Loop();

    // make a modset which we will fill in the new modset data from.
    // this uses a cloned ID as we need to distinguish the modsets
    // we are generating during this pass from the modsets we generated
    // during a previous pass.
    BlockId *mod_id = BlockId::Make(id->Kind(), function, loop, true);
    BlockModset *mod = BlockModset::Make(mod_id);

    if (!TimerAlarm::ActiveExpired())
      mod->ComputeModset(mem, indirect);

    logout << "Computed modset:" << endl << mod << endl;
    block_mods->PushBack(mod);

    // add an entry to the modset cache. we process the function CFGs from
    // innermost loop to the outermost function, and will add loop modsets
    // to the cache as we go.
    BlockModsetCache.Insert(id, mod);

    if (print_memory.IsSpecified()) {
      logout << "Computed memory:" << endl;
      mem->Print(logout);
      logout << endl;
    }

    block_mems->PushBack(mem);
    logout << endl;

    if (TimerAlarm::ActiveExpired()) {
      logout << "ERROR: Timeout while generating memory: ";
      PrintTime(TimerAlarm::ActiveElapsed());
      logout << endl;

      had_timeout = true;
    }

    TimerAlarm::ClearActive();
  }

  return !had_timeout;
}

// how often to print allocation/timer information.
#define PRINT_FREQUENCY 50
size_t g_print_counter = 0;

void RunAnalysis(const Vector<const char*> &functions)
{
  static BaseTimer analysis_timer("xmemlocal_main");
  Transaction *t = new Transaction();

  // we will manually manage clearing of entries in the modset cache.
  BlockModsetCache.SetLruEviction(false);

  // setup the callgraph sort or worklist seed.
  DoInitTransaction(t, functions);
  t->Clear();

  // current stage being processed.
  size_t current_stage = 0;

  // whether we've processed any functions in the current stage.
  bool current_stage_processed = false;

  // whether we've had an empty function in the current stage.
  bool current_stage_waited = false;

  while (true) {
    Timer _timer(&analysis_timer);

    g_print_counter++;

    if (g_print_counter % PRINT_FREQUENCY == 0) {
      PrintTimers();
      PrintAllocs();
    }

    // currently memory usage for xmemlocal can balloon (not sure what's
    // causing this). There's no real way to get memory usage on Linux
    // (getrusage is broken) so just die every so often. TODO: fix this.
    if (IsAnalysisRemote() && g_print_counter == 5000) {
      logout << "Restarting process, function threshold reached." << endl;
      ClearBlockCaches();
      ClearMemoryCaches();
      AnalysisFinish(1);
    }

    size_t stage_result = t->MakeVariable(true);
    size_t body_data_result = t->MakeVariable(true);
    size_t modset_data_result = t->MakeVariable(true);

    DoFetchTransaction(t, stage_result, body_data_result, modset_data_result);

    size_t new_stage = t->LookupInteger(stage_result)->GetValue();

    if (new_stage > current_stage) {
      // drop any modsets we have cached, these may change after
      // we start the next stage.
      BlockModsetCache.Clear();

      if (g_stage_limit > 0) {
        if (new_stage >= g_stage_limit) {
          logout << "Finished functions [#" << new_stage
                 << "]: hit pass limit" << endl;
          break;
        }
      }

      // if we never processed anything from the old stage (and didn't
      // get an item for the new stage), either the worklist has been drained
      // or has become so small there's not enough work for this process.
      if (new_stage > g_stage_count && !current_stage_processed &&
          !t->Lookup(body_data_result, false)) {
        logout << "Finished functions [#" << new_stage
               << "]: exhausted worklist" << endl;
        break;
      }

      if (IsAnalysisRemote())
        logout << "New stage [#" << new_stage << "]" << endl;

      current_stage = new_stage;
      current_stage_processed = false;
      current_stage_waited = false;
    }

    if (!t->Lookup(body_data_result, false)) {
      // there are no more functions in this stage. sleep if this is the second
      // or later time we've had to wait for this stage, the backend is stalled
      // waiting for another worker to finish generating a modset.
      t->Clear();

      if (current_stage_waited)
        sleep(1);
      current_stage_waited = true;
      continue;
    }

    // we have a function to process.
    current_stage_processed = true;

    Vector<BlockCFG*> block_cfgs;
    BlockCFGUncompress(t, body_data_result, &block_cfgs);

    Assert(!block_cfgs.Empty());
    String *function = block_cfgs[0]->GetId()->Function();

    Vector<BlockModset*> old_mods;
    TOperandString *modset_data = t->LookupString(modset_data_result);
    BlockModsetUncompress(t, modset_data, &old_mods);

    // done with the transaction's returned data.
    t->Clear();

    Vector<Variable*> callees;
    Vector<BlockMemory*> block_mems;
    Vector<BlockModset*> block_mods;

    logout << "Generating memory [#" << current_stage << "] "
           << "'" << function->Value() << "'" << endl << flush;

    GetCalleeModsets(t, block_cfgs, current_stage, &callees);
    bool success = GenerateMemory(block_cfgs, current_stage,
                                  &block_mems, &block_mods);

    if (success) {
      // write out the generated memory and modsets. modsets use a special
      // backend function so that they are not visible until the stage ends.

      TOperand *body_key = new TOperandString(t, function->Value());
      TOperandString *memory_arg = BlockMemoryCompress(t, block_mems);

      t->PushAction(Backend::XdbReplace(t, MEMORY_DATABASE,
                                        body_key, memory_arg));

      TOperandString *modset_arg = BlockModsetCompress(t, block_mods);
      t->PushAction(Backend::BlockWriteModset(t, body_key, modset_arg));

      if (current_stage > g_stage_count) {
        // if the computed modset for the outer function has changed then
        // add all callers to the worklist for the next stage.
        Assert(!block_mods.Empty() && !old_mods.Empty());

        BlockModset *new_mod = block_mods.Back();
        BlockModset *old_mod = old_mods.Back();

        Assert(new_mod->GetId()->IsClone());
        Assert(new_mod->GetId()->Kind() == B_Function);
        Assert(old_mod->GetId()->Kind() == B_Function);
        Assert(new_mod->GetId()->BaseVar() == old_mod->GetId()->BaseVar());

        if (new_mod->MergeModset(old_mod)) {
          // add all the callers of this function to the next worklist.
          TRANSACTION_MAKE_VAR(caller_list);
          TRANSACTION_MAKE_VAR(caller_key);

          t->PushAction(Backend::HashLookup(t, MODSET_DEPENDENCY_HASH,
                                            body_key, caller_list_var));

          TActionIterate *caller_iter =
            new TActionIterate(t, caller_key_var, caller_list);
          caller_iter->PushAction(
            Backend::HashInsertKey(t, WORKLIST_FUNC_NEXT, caller_key));
          t->PushAction(caller_iter);

          logout << "ModsetChanged [#" << current_stage << "]: "
                 << function->Value() << endl;
        }
      }
      else if (current_stage == g_stage_count) {
        // write out all dependencies this function has on callee modsets.
        for (size_t ind = 0; ind < callees.Size(); ind++) {
          String *callee = callees[ind]->GetName();
          size_t callee_len = strlen(callee->Value()) + 1;

          Buffer *buf = new Buffer(200);
          t->AddBuffer(buf);
          buf->Append(callee->Value(), callee_len);
          TOperandString *callee_key =
            new TOperandString(t, buf->base, callee_len);

          t->PushAction(Backend::HashInsertValue(t, MODSET_DEPENDENCY_HASH,
                                                 callee_key, body_key));
        }

        // add this function to the next worklist.
        t->PushAction(Backend::HashInsertKey(t, WORKLIST_FUNC_NEXT, body_key));
      }

      SubmitTransaction(t);
      t->Clear();

      // write out any indirect callgraph edges we generated.
      WritePendingEscape();
    }
  }

  t->Clear();

  if (!functions.Empty()) {
    delete t;
    return;
  }

  // compute memory for global variables.

  t->PushAction(Backend::Compound::HashCreateXdbKeys(t, WORKLIST_GLOB_HASH,
                                                     INIT_DATABASE));
  SubmitTransaction(t);
  t->Clear();

  while (true) {
    Timer _timer(&analysis_timer);

    size_t init_key_result = t->MakeVariable(true);
    size_t init_data_result = t->MakeVariable(true);

    t->PushAction(
      Backend::Compound::HashPopXdbKey(
        t, WORKLIST_GLOB_HASH, INIT_DATABASE,
        init_key_result, init_data_result));
    SubmitTransaction(t);

    TOperandString *init_key = t->LookupString(init_key_result);

    if (init_key->GetDataLength() == 1) {
      // done with all globals.
      t->Clear();
      break;
    }

    Vector<BlockCFG*> block_cfgs;
    BlockCFGUncompress(t, init_data_result, &block_cfgs);

    t->Clear();

    String *global = block_cfgs[0]->GetId()->Function();
    logout << "Generating initializer memory "
           << "'" << global->Value() << "'" << endl << flush;

    Vector<BlockMemory*> block_mems;

    for (size_t ind = 0; ind < block_cfgs.Size(); ind++) {
      if (uint32_t timeout = GetTimeout())
        TimerAlarm::StartActive(timeout);

      BlockCFG *cfg = block_cfgs[ind];
      BlockId *id = cfg->GetId();

      if (print_cfgs.IsSpecified())
        logout << cfg << endl;

      BlockMemory *mem =
        BlockMemory::Make(id, MSIMP_Scalar, MALIAS_Buffer, MCLB_Modset);

      mem->SetCFG(cfg);
      mem->ComputeTables();

      block_mems.PushBack(mem);
      TimerAlarm::ClearActive();
    }

    init_key = new TOperandString(t, global->Value());
    TOperandString *memory_data_arg = BlockMemoryCompress(t, block_mems);

    t->PushAction(Backend::XdbReplace(t, MEMORY_DATABASE,
                                      init_key, memory_data_arg));
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

  print_cfgs.Enable();
  print_memory.Enable();
  print_indirect_calls.Enable();
  pass_limit.Enable();

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
