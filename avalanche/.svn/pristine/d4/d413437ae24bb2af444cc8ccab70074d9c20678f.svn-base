/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*------------------------------------ LocalExecutor.cpp ---------------------------------*/
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
#include <string>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/resource.h>

#include "Logger.h"
#include "LocalExecutor.h"
#include "FileBuffer.h"

using namespace std;

static Logger *logger = Logger::getLogger();

int LocalExecutor::exec(bool setlimit)
{
    child_pid = fork();

    if (child_pid == (pid_t)(-1)) return -1; // Error occures
    if (child_pid != (pid_t)(0))  
    {
      //LOG(logger, "child_pid=" << child_pid);
      return  0; // Parent process
    }

    string args_log;
    for (int i = 0; args[i]; i++) {
        args_log.append(" ");
        args_log.append(args[i]);
    }
    LOG(Logger::DEBUG, "Executing command: " << prog << ", with args: " << args_log);
    
    do_redirect(STDOUT_FILENO, file_out); file_out = -1;
    do_redirect(STDERR_FILENO, file_err); file_err = -1;

    if (setlimit) {
        struct rlimit r;
        r.rlim_cur = RLIM_INFINITY;
        r.rlim_max = RLIM_INFINITY;
        setrlimit(RLIMIT_STACK, &r);
    }

    return execvp(prog, args);
}

int LocalExecutor::wait()
{
    int   status;
    //LOG(logger, "Waiting for child_pid=" << child_pid);
    pid_t ret_proc = ::waitpid(child_pid, &status, 0);
    //LOG(logger, "Process is over ret_proc=" << ret_proc);

    if (ret_proc == (pid_t)(-1)) return -1;

    try
    {
        string f_name = file_err_name;
        FileBuffer error_f(f_name);
        char *err_start;
        if ((err_start = strstr(error_f.buf, "valgrind:")) != NULL)
        {
            LOG(Logger::ERROR, err_start);
            return 1;
        }
    }
    catch (...)
    {
        return 1;
    }

    if (WIFEXITED(status))
    {
        return 0;
    }
    else
    {
        return -1;
    }
}

int LocalExecutor::redirect_stdout(char *file_name)
{
    file_out = open(file_name, O_CREAT | O_TRUNC | O_WRONLY, 
                    S_IRUSR | S_IROTH | S_IRGRP | S_IWUSR | S_IWOTH | S_IWGRP);
    if (file_out == -1)
    {
        LOG(Logger::JOURNAL, "Cannot open " << file_name << strerror(errno));
        return -1;
    }
    return 0;
}

int LocalExecutor::redirect_stderr(char *file_name)
{
    file_err_name = strdup(file_name);
    file_err = open(file_name, O_CREAT | O_TRUNC | O_WRONLY, 
                    S_IRUSR | S_IROTH | S_IRGRP | S_IWUSR | S_IWOTH | S_IWGRP);
    if (file_err == -1)
    {
        LOG(Logger::JOURNAL, "Cannot open " << file_name << strerror(errno));
        return -1;
    }
    return 0;
}

int LocalExecutor::do_redirect(int file_to_redirect, int new_file)
{
    if (new_file == -1) return -1;

    dup2(new_file, file_to_redirect);
    close(new_file);
    return 0;
}

LocalExecutor::~LocalExecutor()
{ 
    if (file_out != -1) 
    {
      close(file_out);
    }
    if (file_err != -1) 
    {
      close(file_err);
    }
    if (prog != NULL)
    {
        free(prog);
    }
    if (file_err_name != NULL)
    {
        free(file_err_name);
    }
}

