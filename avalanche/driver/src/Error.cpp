//*---------------------------------------------------------------------------*/
/*------------------------------- AVALANCHE ---------------------------------*/
/*- Driver. Coordinates other processes, traverses conditional jumps tree.  -*/
/*-------------------------------- Error.h ----------------------------------*/
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

#include <cerrno>
#include <cstring>

#include "Error.h"
#include "Logger.h"

using namespace std;

enum {
    PLAIN,
    VERBOSE,
    ERROR_LOG
};

static const errorInfo error_pattern[] = {
                {CRASH_TERMINATED, ""},
                {CRASH_SIGALRM, ""},
                {MC_UNINIT, "uninitialised"},
                {MC_UNADDR, "unaddressable"},
                {MC_INVALID_R, "Invalid read"},
                {MC_INVALID_W, "Invalid write"},
                {MC_INVALID_FREE, "Invalid free"},
                {MC_INVALID_MEM, "Mismatched"},
                {MC_OVERLAP, "Source and destination overlap"},
                {MC_DEF_LOST, "are definitely lost"},
                {MC_POSS_LOST, "are possibly lost"},
                {HG_LOCK_ORDER, "lock order"},
                {HG_PTHREAD_API, "call to"},
                {HG_UNLOCK_INVALID, "unlocked an invalid lock"},
                {HG_UNLOCK_FOREIGN, "currently held by"},
                {HG_UNLOCK_UNLOCKED, "unlocked a not-locked lock"},
                {HG_DATA_RACE, "Possible data race"},
                {UNKNOWN, ""}};

static Logger* logger = Logger::getLogger();

int Error::error_num = 0;
int Error::subtype_num[NO_CHECK];

Error::Error(int _type, int _status) : type(_type), status(_status)
{
    id = Error::error_num ++;
}

void Error::initCounters()
{
    for (int i = 0; i < NO_CHECK; i ++)
    {
        subtype_num[i] = 0;
    }
}

int Error::getFilterCode(string plugin_name)
{
    if (plugin_name == "covgrind") {
        return CRASH;
    }
    else if (plugin_name == "memcheck") {
        return MC_MEMORY;
    }
    else if (plugin_name == "helgrind") {
        return HG_THREAD;
    }
    else {
        return NO_CHECK;
    }
}
        
        
pair<int, int> Error::getFilterLimits(int filter)
{
    switch(filter)
    {
        case CRASH:
        case NO_CHECK:  return make_pair<int,int>(UNKNOWN, UNKNOWN);
        case MC_MEMORY: return make_pair<int,int>(MC_UNINIT, MC_POSS_LOST);
        case HG_THREAD: return make_pair<int,int>(HG_LOCK_ORDER, HG_DATA_RACE);
        default:        return make_pair<int,int>(MC_UNINIT, UNKNOWN - 1);
    }
}

char* Error::match(char* source, errorInfo &result, int filter)
{
    char* min_pos = NULL, *temp_pos;
    int i, min_index = -1;
    pair<int, int> error_limits = Error::getFilterLimits(filter);
    if (error_limits.first == UNKNOWN)
    {
        return NULL;
    }
    for (i = error_limits.first; i <= error_limits.second; i ++)
    {
        temp_pos = strstr(source, error_pattern[i].pattern);
        if (temp_pos != NULL)
        {
            if ((min_pos == NULL) || (temp_pos < min_pos))
            {
                min_pos = temp_pos;
                min_index = i;
            }
        }
    }
    if (min_index < 0)
    {
        min_index = UNKNOWN;
    }
    result = error_pattern[min_index];
    while (min_pos >= source)
    {
        if (*min_pos == '\n') break;
        min_pos --;
    }
    return min_pos;
}

int Error::getSubtypeNumber()
{
    int subtype = getType();
    if ((subtype >= 0) && (subtype < NO_CHECK))
    {
        return subtype_num[subtype];
    }
}

void Error::incSubtypeNumber()
{
    int subtype = getType();
    if ((subtype >= 0) && (subtype < NO_CHECK))
    {
        subtype_num[subtype] ++;
    }
}

void Error::setTrace(string _trace)
{
    trace = _trace;
}

string Error::getTrace()
{
    return trace;
}

string Error::getTraceBody()
{
    unsigned int endl_pos = trace.find("\n");
    if (endl_pos != string::npos)
    {
        return trace.substr(endl_pos + 1);
    }
    return string("");
}

string Error::getTraceHeader()
{
    unsigned int endl_pos = trace.find("\n");
    if (endl_pos != string::npos)
    {
        return trace.substr(0, endl_pos);
    }
    return string("");
}

void Error::setCommand(string _command)
{
    command = _command;
}

void Error::updateCommand(string _command)
{
    all_command += _command + string("\n");
}

string Error::getCommand()
{
    return command;
}

void Error::setTraceFile(string _trace_file)
{
    trace_file = _trace_file;
}

string Error::getTraceFile()
{
    return trace_file;
}

void Error::setStatus(int _status)
{
    status = _status;
}

int Error::getStatus()
{
    return status;
}

void Error::addInput(int _input)
{
    inputs.insert(_input);
}

string Error::getSummary(string prefix, int input_num, bool verbose)
{
    string input_file_m;
    input_file_m = prefix + getFileNameModifier() + "_";
    ostringstream out_stream;
    out_stream << endl << " Error #" << id << ": ";
    if (verbose)
    {
        out_stream << getTraceHeader() << endl;
    }
    else
    {
        out_stream << getShortName() << endl;
    }
    if (input_num != 0)
    {
        out_stream << "  Inputs: ";
    }
    for (set<int>::iterator it = inputs.begin();
                            it != inputs.end();
                            it ++)
    {

        if (it == inputs.begin())
        {
            out_stream << "  ";
        }
        if (input_num < 0)
        {
            out_stream << input_file_m << *it;
        }
        else if (input_num > 0)
        {
            for (int i = 0; i < input_num; i ++)
            {
                out_stream << input_file_m << *it << "_" << i;
                if (i < input_num - 1)
                {
                    out_stream << ", ";
                }
            }
        }
        else
        {
            break;
        }
        if (verbose)
        {
            out_stream << endl;
        }
        else
        {
            out_stream << "; ";
        }
    }
    out_stream << endl;
    if (verbose && (trace != ""))
    {
            out_stream << "  Stack trace:" << endl << "  " << trace << endl;
    }
    if (trace == "")
    {
        out_stream << "  Warning: application was likely terminated"
                      " by SIGKILL signal.\n  Manual checking is required"
                      " to validate the error.\n";
    }
    if (status == OTHER_SIGNAL)
    { 
        out_stream << "  Warning: terminating signal wasn't sent by kernel"
                      " or the analyzed process.\n  Manual checking is required to"
                      " validate the error.\n";
    }
    out_stream << "  Command: " << command << endl;
    return out_stream.str();
}

string Error::getList()
{
    ostringstream out_stream;
    out_stream << "Error " << id << endl;
    out_stream << trace << endl;
    out_stream << all_command << endl << endl;
    return out_stream.str();
}

int Error::getType()
{
    if (type <= CRASH_SIGALRM)
    {
        return CRASH;
    }
    if (type <= MC_POSS_LOST)
    {
        return MC_MEMORY;
    }
    if (type <= HG_DATA_RACE)
    {
        return HG_THREAD;
    }
    return UNKNOWN;
}

string Error::getShortName()
{
    string result = "Received ";
    size_t pos;
    switch (type)
    {
        case CRASH_TERMINATED:
                if ((pos = trace.find("SIG")) != string::npos)
                {
                    result += trace.substr(pos, trace.find(')') - pos);
                }
                else
                {
                    result += "signal";
                }
                return result;
        case CRASH_SIGALRM:
                return string("Received SIGALRM (possible infinite loop)");
        case MC_UNINIT:
                return string("Use of uninitialized byte(s)");
        case MC_UNADDR:
                return string("Use of unaddressable byte(s)");
        case MC_INVALID_R:
                return string("Invalid read");
        case MC_INVALID_W:
                return string("Invalid write");
        case MC_INVALID_FREE:
                return string("Invalid free/delete");
        case MC_INVALID_MEM:
                return string("Mismatched alloc/dealloc functions");
        case MC_OVERLAP:
                return string("Source and destination overlap");
        case MC_DEF_LOST:
                return string("Definite memory loss");
        case MC_POSS_LOST:
                return string("Possible memory loss");
        case HG_LOCK_ORDER:
                return string("Lock order violated");
        case HG_PTHREAD_API:
                return string("Call to pthread function failed");
        case HG_UNLOCK_INVALID:
                return string("Invalid lock unlocked");
        case HG_UNLOCK_FOREIGN:
                return string("Foreign lock unlocked");
        case HG_UNLOCK_UNLOCKED:
                return string("Double unlock");
        case HG_DATA_RACE:
                return string("Possible data race");
        default:return string("Unknown error");
    }
}

string Error::getFileNameModifier()
{
    if (type <= CRASH_SIGALRM)
    {
        return "exploit";
    }
    if (type <= MC_POSS_LOST)
    {
        return "memcheck";
    }
    if (type <= HG_DATA_RACE)
    {
        return "concurrency";
    }
    return "unknown";
}
