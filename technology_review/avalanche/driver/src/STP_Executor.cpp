/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*--------------------------------- STP_Executor.cpp -------------------------------------*/
/*----------------------------------------------------------------------------------------*/

/*
   Copyright (C) 2009 Ildar Isaev
      iisaev@ispras.ru
   Copyright (C) 2009 Nick Lugovskoy
      lugovskoy@ispras.ru

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

#include <cerrno>
#include <cstring>
#include <cstdlib>

#include "Logger.h"
#include "STP_Executor.h"
#include "TmpFile.h"
#include "Monitor.h"

using namespace std;

extern int thread_num;
extern Monitor* monitor;

static Logger *logger = Logger::getLogger();


STP_Executor::STP_Executor(bool debug_full_enable,
                           const string &install_dir):
                               debug_full(debug_full_enable)
{
    prog = strdup((install_dir + "../lib/avalanche/stp").c_str());

    argsnum = 4;

    args = (char **)calloc(argsnum, sizeof(char *));

    args[0] = strdup(prog);
    args[1] = strdup("-p");
}

string STP_Executor::run(const char *file_name, int thread_index)
{
    if (!thread_num)
    {
      LOG(Logger :: DEBUG, "Running STP.");
    }
    else
    {
      LOG(Logger :: DEBUG, "Thread #" << thread_index << ": Running STP.");
    }
    
    args[2] = strdup(file_name);

    TmpFile* file_out = new TmpFile();
    TmpFile* file_err = new TmpFile();

    monitor->setTmpFiles(file_out, file_err);

    if ((redirect_stdout(file_out->getName()) == -1) ||
        (redirect_stderr(file_err->getName()) == -1))
    {
        return string("");
    }

    int ret = exec(true);
    monitor->setPID(child_pid, thread_index);
 
    if (ret == -1) {
        LOG(Logger :: ERROR, "Problem in execution: " << strerror(errno));
        return string("");
    }

    ret = wait();
    if (ret == -1) {
        if (!monitor->getKilledStatus())
        {
          LOG(Logger :: ERROR, "Problem in waiting: " << strerror(errno));
        }
        return string("");
    }
    if (!thread_num)
    {
      LOG(Logger :: DEBUG, "STP is finished.");
    }
    else
    {
      LOG(Logger :: DEBUG, "Thread #" << thread_index << ": STP is finished.");
    }

    if (ret != 0) {
        LOG(Logger :: DEBUG, "STP exits with code " << ret);
        return string("");
    }

    return file_out->getName();
}

STP_Executor::~STP_Executor()
{
}

