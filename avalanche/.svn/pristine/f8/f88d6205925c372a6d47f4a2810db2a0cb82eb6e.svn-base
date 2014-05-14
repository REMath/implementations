/*---------------------------------------------------------------------------*/
/*------------------------------- AVALANCHE ---------------------------------*/
/*-- Driver. Coordinates other processes, traverses conditional jumps tree. -*/
/*------------------------------ Monitor.cpp --------------------------------*/
/*---------------------------------------------------------------------------*/

/*
   Copyright (C) 2010-2011 Michael Ermakov
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

#include <sstream>
#include <signal.h>
#include <algorithm>
#include <iterator>
#include <iomanip>

#include "Monitor.h"

using namespace std;

Monitor::Monitor(string checker_name, time_t _global_start_time)
{
    is_killed = false;
    global_start_time = _global_start_time;
    network_overhead = 0;
    module_name[CHECKER] = checker_name;
    module_name[TRACER] = "tracegrind";
    module_name[STP] = "stp";
}


SimpleMonitor::SimpleMonitor(string checker_name, time_t _global_start_time) : 
                                     Monitor(checker_name, _global_start_time),
                                     current_state(OUT), cur_tmp_stdout(NULL),
                                     cur_tmp_stderr(NULL)
{
    for (int i = 0; i < MODULE_COUNT; i ++)
    {
        module_time[i] = 0;
    }
}
                        
void SimpleMonitor::addTime(time_t end_time, unsigned int thread_index)
{
    if (current_state != OUT)
    {
        module_time[current_state] += end_time - start_time;
        current_state = OUT;
    }
}

void SimpleMonitor::setTmpFiles(TmpFile* tmp_stdout, TmpFile* tmp_stderr)
{
    if (cur_tmp_stdout != NULL) 
    {
        delete cur_tmp_stdout;
        delete cur_tmp_stderr;
    }
    cur_tmp_stdout = tmp_stdout;
    cur_tmp_stderr = tmp_stderr;
}

void SimpleMonitor::removeTmpFiles()
{
    delete cur_tmp_stdout;
    delete cur_tmp_stderr;
    cur_tmp_stdout = NULL;
    cur_tmp_stderr = NULL;
}

                        
string SimpleMonitor::getStats(time_t global_time)
{
    ostringstream result;
    for (int i = 0; i < MODULE_COUNT; i ++)
    {
        result << module_name[i] << ": " << module_time[i];
        if (global_time != 0)
        {
            result << " (" << 
                     100.0 * ((double) module_time[i]) / global_time << " %)";
        }
        result << ((i == MODULE_COUNT - 1) ? "" : ", ");
    }
    if (network_overhead != 0)
    {
        result << ", network overhead: " << network_overhead;
    }
    result << ".";
    return result.str();
}

void SimpleMonitor::handleSIGKILL()
{
    if (current_state != OUT)
    {
        kill(current_pid, SIGKILL);
        addTime(time(NULL));
    }
}

void SimpleMonitor::handleSIGALARM()
{ 
    kill(current_pid, SIGKILL); 
}

ParallelMonitor::ParallelMonitor(string checker_name, 
                                 time_t _global_start_time, 
                                 unsigned int _thread_num)
                                                                                                                                                                 : Monitor(checker_name, _global_start_time)
{
    pthread_mutex_init(&add_time_mutex, NULL);
    checker_alarm = 0;
    tracer_alarm = 0;
    tracer_time = 0;
    thread_num = _thread_num;
    current_state = new state[thread_num + 1];
    checker_start_time = new time_t[thread_num];
    stp_start_time = new time_t[thread_num];
    current_pid = new pid_t[thread_num + 1];
    alarm_killed = new bool[thread_num];
    for (int i = 0; i < thread_num; i ++)
    {
        alarm_killed[i] = false;
        current_state[i] = OUT;
        checker_start_time[i] = stp_start_time[i] = 0;
    }

}

ParallelMonitor::~ParallelMonitor()
{
    delete []current_state;
    delete []checker_start_time;
    delete []stp_start_time;
    delete []current_pid;
    delete []alarm_killed;
    pthread_mutex_destroy(&add_time_mutex);
}

void ParallelMonitor::setState(state _state, time_t _start_time, 
                               unsigned int thread_index)
{
    current_state[thread_index] = _state;
    if (_state == STP)
    {
        stp_start_time[thread_index - 1] = _start_time;
    }
    else if (_state == CHECKER)
    {
        if (!thread_index)
        {
            thread_index = 1;
        }
        checker_start_time[thread_index - 1] = _start_time;
        alarm_killed[thread_index - 1] = false;
    }
    else if (_state == TRACER)
    {
        tracer_start_time = _start_time;
    }
}

void ParallelMonitor::setTmpFiles(TmpFile* tmp_stdout, TmpFile* tmp_stderr)
{
    pthread_mutex_lock(&add_time_mutex);
    tmp_files.push_back(make_pair(tmp_stdout, tmp_stderr));
    pthread_mutex_unlock(&add_time_mutex);
}

void ParallelMonitor::removeTmpFiles()
{
    pthread_mutex_lock(&add_time_mutex);
    for (vector<pair<TmpFile*, TmpFile*> >::iterator i = tmp_files.begin(); 
                                                     i != tmp_files.end();
                                                     i ++)
    {
        delete i->first;
        delete i->second;
    }
    tmp_files.clear();
    pthread_mutex_unlock(&add_time_mutex);
}

void ParallelMonitor::addTime(time_t end_time, unsigned int thread_index)
{
    pthread_mutex_lock(&add_time_mutex);
    if (current_state[thread_index] == TRACER)
    {
        if (tracer_start_time != 0)
        {
            tracer_time += end_time - tracer_start_time;
            current_state[thread_index] = OUT;
            tracer_start_time = 0;
        }
    }
    else if (current_state[thread_index] != OUT)
    {
        time_t st_time;
        if (!thread_index)
        {
            st_time = checker_start_time[thread_index];
            thread_index = 1;
        }
        else
        {
            st_time = (current_state[thread_index] == CHECKER) ? 
                                checker_start_time[thread_index - 1] : 
                                stp_start_time[thread_index - 1];
        }
        if ((end_time > st_time) && (st_time != 0))
        {
            interval new_interval;
            new_interval.first = st_time - global_start_time;
            new_interval.second = end_time - global_start_time;
            if (current_state[thread_index] == CHECKER)
            {
                checker_time.insert(new_interval);
                checker_start_time[thread_index - 1] = 0;
            }
            else
            {
                stp_time.insert(new_interval);
                stp_start_time[thread_index - 1] = 0;
            }
            current_state[thread_index] = OUT;
        }
    }
    pthread_mutex_unlock(&add_time_mutex);
}

static set <time_t> getRealTimeSet(const set <interval> &time_set)
{
    set <time_t> unique_set;
    for (set <interval>::iterator i = time_set.begin(); 
                                  i != time_set.end(); 
                                  i ++)
    {
        for (time_t j = (*i).first; j != (*i).second; j ++)
        {
            unique_set.insert(j);
        }
    }
    return unique_set;
}

string ParallelMonitor::getStats(time_t global_time)
{
    ostringstream result;
    set <time_t> tmp_set, real_stp_set, real_checker_set;
#define EXTENDED_MODULE_COUNT 4
    time_t module_time[EXTENDED_MODULE_COUNT];
    real_checker_set = getRealTimeSet(checker_time);
    real_stp_set = getRealTimeSet(stp_time);
    module_time[TRACER_OUTPUT] = tracer_time;
    set_difference(real_checker_set.begin(), real_checker_set.end(), 
                   real_stp_set.begin(), real_stp_set.end(), 
                   inserter(tmp_set, tmp_set.begin()));
    module_time[CHECKER_OUTPUT] = tmp_set.size();
    tmp_set.clear();
    set_difference(real_stp_set.begin(), real_stp_set.end(), 
                   real_checker_set.begin(), real_checker_set.end(), 
                   inserter(tmp_set, tmp_set.begin()));
    module_time[STP_OUTPUT] = tmp_set.size();
    tmp_set.clear();
    set_intersection(real_stp_set.begin(), real_stp_set.end(), 
                     real_checker_set.begin(), real_checker_set.end(), 
                     inserter(tmp_set, tmp_set.begin()));
    module_time[CHECKER_AND_STP_OUTPUT] = tmp_set.size();
    string extended_module_name[EXTENDED_MODULE_COUNT];
    for (int i = 0; i < MODULE_COUNT; i ++)
    {
        extended_module_name[i] = 
                (i == 0) ? module_name[i] : (module_name[i] + string(" only"));
    }
    extended_module_name[CHECKER_AND_STP_OUTPUT] = 
                module_name[CHECKER] + string(" & ") + module_name[STP];
    result << setiosflags(ios::fixed) << setprecision(4);
    for (int i = 0; i < EXTENDED_MODULE_COUNT; i ++)
    {
        result << extended_module_name[i] << ": " << module_time[i];
        if (global_time != 0)
        { 
            double percentage = 
                    100.0 * ((double) module_time[i]) / ((double) global_time);
            result << " (" << percentage << "%)";
        }
        result << ((i == EXTENDED_MODULE_COUNT - 1) ? "" : ", ");
    }
#undef EXTENDED_MODULE_COUNT
    if (network_overhead != 0)
    {
        result << ", network overhead: " << network_overhead;
    }
    return result.str();
}

void ParallelMonitor::handleSIGKILL()
{
    for (int i = 0; i < thread_num + 1; i ++)
    {
        if ((current_state[i] != OUT) && (current_pid[i] != 0))
        {
            addTime(time(NULL), i);
            kill(current_pid[i], SIGKILL);
        }
    }
}

void ParallelMonitor::handleSIGALARM()
{ 
    time_t cur_time = time(NULL);
    if (current_state[0] = TRACER)
    {
        if ((tracer_alarm > 0) && 
            (cur_time - tracer_start_time >= tracer_alarm))
        {
            kill(current_pid[0], SIGALRM);
        }
    }
    else if (checker_alarm > 0)
    {
        for (int i = 0; i < thread_num; i ++)
        {
            if ((current_state[i + 1] == CHECKER) && 
                (cur_time - checker_start_time[i] >= checker_alarm))
            {
                alarm_killed[i] = true;
                kill(current_pid[i + 1], SIGALRM);
            }
        }
    }
}
