
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

#include <unistd.h>
#include <backend/backend_compound.h>
#include <imlang/filename.h>
#include <imlang/interface.h>

NAMESPACE_XGILL_USING

const char *USAGE = "xsource [options] < preprocessed_code";

ConfigOption log_file(CK_String, "log", "",
                      "file to receive log messages");

ConfigOption base_dir(CK_String, "basedir", "",
                      "prefix to remove from generated file paths");

ConfigOption end_manager(CK_Flag, "end-manager", NULL,
                         "signal manager to finish (ignore other input)");

int main(int argc, const char **argv)
{
  trans_remote.Enable();
  log_file.Enable();
  base_dir.Enable();
  end_manager.Enable();

  Vector<const char*> unspecified;
  bool parsed = Config::Parse(argc, argv, &unspecified);
  if (!parsed || !unspecified.Empty()) {
    Config::PrintUsage(USAGE);
    return 1;
  }

  AnalysisPrepare();

  if (end_manager.IsSpecified()) {
    SubmitInitialTransaction();
    SubmitFinalTransaction();
    AnalysisFinish(0);
  }

  // need to use a FILE handle for this because we'll be appending.
  FILE *log_handle = NULL;

  if (log_file.IsSpecified()) {
    log_handle = fopen(log_file.StringValue(), "a");
    Assert(log_handle);

    XIL_SetLogFile(log_handle);
  }

  char *cwd = getcwd(NULL, 0);
  SetWorkingDirectory(cwd);

  if (base_dir.IsSpecified())
    SetBaseDirectory(base_dir.StringValue());
  else
    SetBaseDirectory(cwd);

  ProcessPreprocessedFile(cin, NULL);

  if (log_handle) {
    fclose(log_handle);
    log_stream = NULL;
  }

  AnalysisFinish(0);
}
