
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
#include <check/checker.h>
#include <check/sufficient.h>
#include <util/config.h>

NAMESPACE_XGILL_USING

const char *USAGE = "xcheck [options] [function-check*]";

ConfigOption check_kind(CK_String, "check-kind", "write_overflow",
                        "assert kind to analyze");

ConfigOption check_types(CK_String, "check-type", "",
                         "bound type to check within assertions");

ConfigOption check_file(CK_String, "check-file", "",
                        "file with list of checks to analyze");

ConfigOption xml_file(CK_String, "xml-out", "",
                      "file to receive XML report for single check");

// number of callgraph stages.
static size_t g_stage_count = 0;

// if we're generating an XML file, the single function to analyze. there can
// be multiple workers using the manager and generating separate XML files,
// and we don't want them to share a worklist.
static Buffer xml_function_buf;

void DoInitTransaction(Transaction *t, const Vector<const char*> &checks)
{
  // don't use the worklist if we're generating an XML file. there can be
  // multiple workers using the manager and generating separate XML files,
  // and we don't want them to share a worklist.
  if (xml_file.IsSpecified()) {
    Assert(checks.Size() == 1);
    Try(BlockSummary::GetAssertFunction(checks[0], &xml_function_buf));
    return;
  }

  size_t count_var = t->MakeVariable(true);

  if (!checks.Empty()) {
    // doing a seed analysis, parse the functions from the check names.
    TOperandList *functions = new TOperandList(t);

    // parse the function names from the assertion format.
    for (size_t uind = 0; uind < checks.Size(); uind++) {
      Buffer *buf = new Buffer();
      t->AddBuffer(buf);

      Try(BlockSummary::GetAssertFunction(checks[uind], buf));
      functions->PushOperand(new TOperandString(t, (const char*) buf->base));
    }

    t->PushAction(Backend::BlockSeedWorklist(t, functions));
  }
  else {
    t->PushAction(Backend::BlockLoadWorklist(t, count_var));
  }

  SubmitTransaction(t);

  if (checks.Empty())
    g_stage_count = t->LookupInteger(count_var)->GetValue();
}

void DoFetchTransaction(Transaction *t, size_t stage_result,
                        size_t body_data_result,
                        size_t memory_data_result, size_t modset_data_result,
                        size_t summary_data_result)
{
  TRANSACTION_MAKE_VAR(body_key);
  TRANSACTION_MAKE_VAR(key_empty);

  if (xml_file.IsSpecified()) {
    // get the single function instead of going to the worklist.
    TOperand *zero = new TOperandInteger(t, 0);
    body_key = new TOperandString(t, (const char*) xml_function_buf.base);
    t->PushAction(new TActionAssign(t, zero, stage_result));
  }
  else {
    t->PushAction(Backend::BlockCurrentStage(t, stage_result));
    t->PushAction(Backend::BlockPopWorklist(t, body_key_var));
  }

  t->PushAction(Backend::StringIsEmpty(t, body_key, key_empty_var));

  TActionTest *non_empty_branch = new TActionTest(t, key_empty, false);
  t->PushAction(non_empty_branch);

  non_empty_branch->PushAction(
    Backend::XdbLookup(
      t, BODY_DATABASE, body_key, body_data_result));
  non_empty_branch->PushAction(
    Backend::XdbLookup(
      t, MEMORY_DATABASE, body_key, memory_data_result));
  non_empty_branch->PushAction(
    Backend::XdbLookup(
      t, MODSET_DATABASE, body_key, modset_data_result));
  non_empty_branch->PushAction(
    Backend::XdbLookup(
      t, SUMMARY_DATABASE, body_key, summary_data_result));

  SubmitTransaction(t);
}

void StoreDisplayPath(DisplayPath *path, char *name, BlockId *id)
{
  static Buffer xml_buf("Buffer_xcheck_xml");
  path->WriteXML(&xml_buf);

  if (xml_file.IsSpecified()) {
    FileOutStream file_out(xml_file.StringValue());
    file_out.Put(xml_buf.base, xml_buf.pos - xml_buf.base);
  }
  else {
    static Buffer key_buf("Buffer_xcheck_key");
    static Buffer compress_buf("Buffer_xcheck_compress");

    // get the compressed XML for the database entry.
    CompressBufferInUse(&xml_buf, &compress_buf);

    Transaction *t = new Transaction();

    // the output database is in the report's name, up to the first '$'.
    char *kind_end = strchr(name, '$');
    Assert(kind_end);
    *kind_end = 0;

    size_t len = kind_end - name + 20;
    char *database = new char[len];
    snprintf(database, len, "report_%s.xdb", name);
    *kind_end = '$';

    TOperand *key_arg = new TOperandString(t, name);
    TOperand *data_arg =
      new TOperandString(t, compress_buf.base,
                         compress_buf.pos - compress_buf.base);
    t->PushAction(Backend::XdbReplace(t, database, key_arg, data_arg));

    SubmitTransaction(t);
    delete t;
    delete[] database;

    key_buf.Reset();
    compress_buf.Reset();
  }

  xml_buf.Reset();
}

// check that an expression has a bound matching the -check-type switch.
class CheckTypeVisitor : public ExpVisitor
{
 public:
  bool found_match;

  CheckTypeVisitor()
    : ExpVisitor(VISK_All), found_match(false)
  {}

  void Visit(Exp *exp)
  {
    if (ExpBound *nexp = exp->IfBound()) {

  Buffer string_buf;
  nexp->GetStrideType()->ToString(&string_buf);
  printf("COMPARE %s %s\n", check_types.StringValue(), (const char*) string_buf.base);

    if (nexp->GetStrideType()->EqualsString(check_types.StringValue()))
      found_match = true;
    }
  }
};

void RunAnalysis(const Vector<const char*> &checks)
{
  static BaseTimer analysis_timer("xcheck_main");
  Transaction *t = new Transaction();

  // construct and submit the worklist create transaction.
  DoInitTransaction(t, checks);
  t->Clear();

  size_t current_stage = 0;

  while (true) {
#ifndef DEBUG
    ResetTimeout(40);
#endif

    Timer _timer(&analysis_timer);

    // construct and submit a worklist fetch transaction.
    size_t stage_result = t->MakeVariable(true);
    size_t body_data_result = t->MakeVariable(true);
    size_t memory_data_result = t->MakeVariable(true);
    size_t modset_data_result = t->MakeVariable(true);
    size_t summary_data_result = t->MakeVariable(true);

    DoFetchTransaction(t, stage_result, body_data_result,
                       memory_data_result, modset_data_result,
                       summary_data_result);

    size_t new_stage = t->LookupInteger(stage_result)->GetValue();

    if (new_stage > current_stage) {
      if (new_stage > g_stage_count) {
        // we've analyzed every function. end the analysis.
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

    Vector<BlockCFG*> function_cfgs;
    BlockCFGUncompress(t, body_data_result, &function_cfgs);

    if (function_cfgs.Empty()) {
      // logout << "WARNING: Missing CFG: "
      //        << (const char*) body_key->GetData() << endl;
      t->Clear();
      continue;
    }

    BlockCFGCacheAddListWithRefs(function_cfgs);

    Vector<BlockMemory*> function_mems;
    BlockMemoryUncompress(t, memory_data_result, &function_mems);
    BlockMemoryCacheAddList(function_mems);

    Vector<BlockModset*> function_mods;
    TOperandString *modset_op = t->LookupString(modset_data_result);
    BlockModsetUncompress(t, modset_op, &function_mods);
    BlockModsetCacheAddList(function_mods);

    Vector<BlockSummary*> function_sums;
    TOperandString *summary_op = t->LookupString(summary_data_result);
    BlockSummaryUncompress(t, summary_op, &function_sums);
    BlockSummaryCacheAddList(function_sums);

    t->Clear();

    const char *function = function_cfgs.Back()->GetId()->Function()->Value();

    logout << "Checking: '" << function << "'" << endl << endl << flush;

    size_t assertion_count = 0;
    size_t redundant_count = 0;
    size_t success_count = 0;
    size_t report_count = 0;

    for (size_t cind = 0; cind < function_cfgs.Size(); cind++) {
      BlockCFG *cfg = function_cfgs[cind];
      BlockId *id = cfg->GetId();

      BlockMemory *mcfg = BlockMemoryCache.Lookup(id);
      BlockSummary *sum = BlockSummaryCache.Lookup(id);

      Assert(sum);
      sum->ComputeAssertNames();

      const Vector<AssertInfo> *asserts = sum->GetAsserts();
      size_t assert_count = VectorSize<AssertInfo>(asserts);

      if (mcfg) {
        mcfg->SetCFG(cfg);
      }
      else {
        // this should be an empty summary since we failed to generate memory
        // for the block.
        Assert(assert_count == 0);
        logout << "WARNING: Missing memory: " << id << endl;
      }

      for (size_t ind = 0; ind < assert_count; ind++) {
        const AssertInfo &info = asserts->At(ind);

        // apply kind and type filters on the assertion, unless we have
        // an explicit list of checks (in which case we'll look at all
        // those specified).
        if (checks.Empty()) {
          if (strcmp(AssertKindString(info.kind), check_kind.StringValue()))
            continue;

          if (check_types.IsSpecified()) {
            CheckTypeVisitor visitor;
            info.bit->DoVisit(&visitor);

            if (!visitor.found_match)
              continue;
          }
        }

        // ignore trivial and redundant assertions.
        if (info.cls != ASC_Check) {
          redundant_count++;
          continue;
        }

        assertion_count++;

        Assert(info.name_buf);
        char *name = (char*) info.name_buf->base;

        if (checks.Size()) {
          // the command line assertions are a filter on the checks we do.
          bool checks_match = false;

          for (size_t ind = 0; ind < checks.Size(); ind++) {
            if (!strcmp(checks[ind], name)) {
              checks_match = true;
              break;
            }
          }

          if (!checks_match)
            continue;
        }

        // reset the hard timeout at each new assertion. we want to avoid hard
        // failures as much as possible; this can make functions take a very
        // long time to analyze in the worst case. hard timeouts are disabled
        // if we're debugging.
#ifndef DEBUG
        ResetTimeout(40);
#endif

        // set a soft timeout for the checker/solver.
        if (uint32_t timeout = GetTimeout())
          TimerAlarm::StartActive(timeout);

        logout << "ASSERTION '" << name << "'" << endl;
        logout << "Point " << info.point << ": " << info.bit << endl;

        CheckerState *state = CheckAssertion(mcfg->GetId(), info);

        Solver *solver = state->GetSolver();
        solver->PrintTimers();

        if (state->GetReportKind() != RK_None) {
          ReportKind report = state->GetReportKind();
          const char *report_string = ReportString(report);

          logout << "REPORT " << report_string;
          logout << " '" << name << "'" << endl;

          state->PrintTraits();

          Assert(state->m_path);
          state->m_path->m_name = name;
          StoreDisplayPath(state->m_path, name, id);

          report_count++;
        }
        else {
          logout << "SUCCESS '" << name << "'" << endl;
          success_count++;
        }

        delete state;

        TimerAlarm::ClearActive();

        logout << endl << flush;
      }

      BlockMemoryCache.Release(id);
      BlockSummaryCache.Release(id);
    }

    BlockCFG *file_cfg = function_cfgs[0];
    const char *file_name = file_cfg->GetBeginLocation()->FileName()->Value();

    Assert(file_name);

    logout << "Finished: '" << function << "'"
         << " FILE " << file_name
         << " REDUNDANT " << redundant_count
         << " ASSERTION " << assertion_count
         << " SUCCESS " << success_count
         << " REPORT " << report_count << endl;

    logout << "Elapsed: ";
    PrintTime(_timer.Elapsed());
    logout << endl << endl << flush;

    // we should analyze the single check our first time through the loop
    // if we're generating an XML file.
    if (xml_file.IsSpecified())
      break;
  }

  delete t;
}

int main(int argc, const char **argv)
{
  timeout.Enable();
  trans_remote.Enable();
  trans_initial.Enable();

  checker_verbose.Enable();
  checker_sufficient.Enable();
  checker_assign.Enable();
  checker_dump.Enable();
  checker_depth.Enable();
  // checker_fixup.Enable();

  solver_use.Enable();
  solver_verbose.Enable();
  solver_constraint.Enable();

  check_kind.Enable();
  check_types.Enable();
  check_file.Enable();
  xml_file.Enable();

  Vector<const char*> checks;
  bool parsed = Config::Parse(argc, argv, &checks);
  if (!parsed) {
    Config::PrintUsage(USAGE);
    return 1;
  }

  // augment the list of checks by reading from a file if necessary.
  Vector<char*> file_checks;
  Buffer check_file_buf;

  if (check_file.IsSpecified()) {
    // read in check names from the specified file.
    FileInStream fin(check_file.StringValue());
    Assert(!fin.IsError());

    ReadInStream(fin, &check_file_buf);
    SplitBufferStrings(&check_file_buf, '\n', &file_checks);

    for (size_t ind = 0; ind < file_checks.Size(); ind++) {
      char *check = file_checks[ind];

      // ignore blank lines.
      if (!*check)
        continue;

      // eat any leading quote.
      if (*check == '\'' || *check == '\"')
        check++;

      // eat any trailing quote.
      size_t length = strlen(check);
      if (check[length - 1] == '\'' || check[length - 1] == '\"')
        check[length - 1] = 0;

      checks.PushBack(check);
    }
  }

  Vector<const char*> new_checks;

  // unescape any HTML markup in the checks.
  for (size_t ind = 0; ind < checks.Size(); ind++)
    new_checks.PushBack(HtmlUnescape(checks[ind]));

  // Solver::CheckSimplifications();

  ResetAllocs();
  AnalysisPrepare();

  if (new_checks.Empty()) {
    if (trans_initial.IsSpecified())
      SubmitInitialTransaction();
    RunAnalysis(new_checks);
    SubmitFinalTransaction();
  }
  else {
    RunAnalysis(new_checks);
  }

  ClearBlockCaches();
  ClearMemoryCaches();
  AnalysisFinish(0);
}
