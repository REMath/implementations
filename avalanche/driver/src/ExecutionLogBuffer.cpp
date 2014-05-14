/*---------------------------------------------------------------------------*/
/*------------------------------- AVALANCHE ---------------------------------*/
/*- Driver. Coordinates other processes, traverses conditional jumps tree.  -*/
/*----------------------------- FileBuffer.cpp ------------------------------*/
/*---------------------------------------------------------------------------*/

/*
   Copyright (C) 2011 Mikhail Ermakov
      mermakov@ispras.ru

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

#include <iostream>
#include <string.h>
#include <stdlib.h>

#include "ExecutionLogBuffer.h"

using namespace std;

ExecutionLogBuffer::ExecutionLogBuffer(std::string _file_name) : 
                                                        FileBuffer(_file_name)
{
    char *summary = strstr(buf, "ERROR SUMMARY");
    if (summary != NULL)
    {
        *summary = '\0';
    }
}

Error* ExecutionLogBuffer::getCrashError()
{
    char *check_pid, *bug_start, *stack_start, *last_bug_line;
    char *last_bug_sym, *tmp, *prev_new_line, *new_buf;
    int eq_num = 0, i = 0, j, skip_length, status = 0;
    
    if (strstr(buf, "Terminated by kernel signal") != NULL)
    {
        status = KERNEL_SIGNAL;
    }
    else if (strstr(buf, "Terminated by self-sent signal") != NULL)
    {
        status = OWN_SIGNAL;
    }
    check_pid = buf;
    for (;;)
    {
        if (check_pid == NULL) return NULL;
        if (*check_pid == '\0') return NULL;
        if (*check_pid == '=') eq_num ++;
        if (eq_num == 4) break;
        check_pid ++;
    }
    skip_length = check_pid - buf + 2;
    Error* new_error;
    if (strstr(buf, "SIGALRM") != NULL)
    {
        new_error = new Error(CRASH_SIGALRM, status);
    }
    else
    {
        new_error = new Error(CRASH_TERMINATED, status);
    }
    bug_start = strstr(buf, "Process terminating");
    if (bug_start == NULL) return new_error;
    stack_start = strstr(bug_start, "at 0x");
    if (stack_start == NULL) return new_error;
    last_bug_line = stack_start;
    last_bug_sym = strchr(last_bug_line, '\n');
    if (last_bug_sym == NULL) return new_error;
    last_bug_line = last_bug_sym + 1;
    prev_new_line = last_bug_sym;
    while (((last_bug_sym = strchr(last_bug_line, '\n')) != NULL) &&
           ((tmp = strstr(last_bug_line, "by 0x")) != NULL) && 
           (tmp < last_bug_sym))
    {
        prev_new_line = last_bug_sym;
        last_bug_line = last_bug_sym + 1;
    }
    last_bug_sym = prev_new_line;
    if (last_bug_sym == NULL) return new_error;
    if (last_bug_sym <= bug_start + 1) return new_error;
    new_buf = (char*) malloc (last_bug_sym - bug_start);
    while (bug_start < last_bug_sym && bug_start != NULL)
    {
        if (*bug_start == '=')
        {
            bug_start += skip_length;
            continue;
        }
        new_buf[i ++] = *bug_start;
        bug_start ++;
    }
    new_buf[i] = '\0';
    
    new_error->setTrace(new_buf);

    free(new_buf);
    
    return new_error;
}

vector<Error*> ExecutionLogBuffer::getErrors(string plugin_name)
{
    char *bug_start, *check_pid, *new_line, *prev_new_line;
    int eq_num = 0, skip_length;
    int filter = Error::getFilterCode(plugin_name);
    errorInfo error_info;
    string trace;
    vector<Error*> result;
    
    bug_start = check_pid = buf;
    for (;;)
    {
        if (check_pid == NULL) return result;
        if (*check_pid == '\0') return result;
        if (*check_pid == '=') eq_num ++;
        if (eq_num == 4) break;
        check_pid ++;
    }
    skip_length = check_pid - buf + 2;
    while ((bug_start = Error::match(bug_start, error_info, filter)) != NULL)
    {
        prev_new_line = bug_start + 1;
        for (;;)
        {
            new_line = strchr(prev_new_line, '\n');
            if (new_line == NULL) return result;
            if (new_line - prev_new_line == skip_length) break;
            trace.append(prev_new_line + skip_length, 
                         new_line - prev_new_line - skip_length + 1);
            prev_new_line = new_line + 1;
        }
        result.push_back(new Error(error_info.error_code, KERNEL_SIGNAL));
        (*result.rbegin())->setTrace(trace);
        trace.clear();
        bug_start = new_line + 1;
    }
    return result;
}
