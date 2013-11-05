/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*------------------------------------- Executor.h ---------------------------------------*/
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

#ifndef __LOCAL_EXECUTOR__H__
#define __LOCAL_EXECUTOR__H__

#include <cstdlib>
#include "Executor.h"


class LocalExecutor : public Executor
{
public:
    LocalExecutor(): prog(NULL), file_out(-1), file_err(-1),
                     file_err_name(NULL) {}

    int exec(bool setlimit);
    int wait();
    int redirect_stdout(char *filename);
    int redirect_stderr(char *filename);
    virtual int run (int thread_index = 0) { return 0; }
    virtual ~LocalExecutor();

protected:
    char  *prog;
    pid_t child_pid;

private:
    int do_redirect(int file_to_redirect, int with_file);

    int file_out;
    int file_err;
    char *file_err_name;
};


#endif //__LOCAL_EXECUTOR__H__

