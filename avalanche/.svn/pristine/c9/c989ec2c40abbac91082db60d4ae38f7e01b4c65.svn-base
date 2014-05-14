/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*------------------------------------- Monitor.h ----------------------------------------*/
/*----------------------------------------------------------------------------------------*/
  
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

#ifndef _MONITOR_H
#define _MONITOR_H

#include <string>
#include <iostream>
#include <set>
#include <utility>
#include <vector>

#include "TmpFile.h"

#define MODULE_COUNT 3

enum state {TRACER, CHECKER, STP, OUT, NETWORK};
enum output {TRACER_OUTPUT,
             CHECKER_OUTPUT,
             STP_OUTPUT,
             CHECKER_AND_STP_OUTPUT};

typedef std::pair<time_t, time_t> interval;
  
class Monitor
{
    protected:
        time_t global_start_time;
        time_t network_overhead;
        bool is_killed;
        std::string module_name[MODULE_COUNT];
    public: 
        Monitor(std::string checker_name, time_t _global_start_time);
        virtual ~Monitor() {}

        virtual void setState(state _state, 
                  time_t _start_time, 
                  unsigned int thread_index = 0) = 0;

        virtual void setPID(pid_t _pid, 
                unsigned int thread_index = 0) = 0;

        virtual void addTime(time_t end_time, 
                 unsigned int thread_index = 0) = 0;

        virtual std::string getStats(time_t global_time = 0) = 0;

        virtual state getCurrentState(unsigned int thread_index = 0) = 0;

        virtual void handleSIGKILL() = 0;
        virtual void handleSIGALARM() = 0;

        virtual void setTmpFiles(TmpFile* tmp_stdout, TmpFile* tmp_stderr) = 0;
        virtual void removeTmpFiles() = 0;

        bool getKilledStatus() 
        { 
            return is_killed; 
        }
        void setKilledStatus(bool _is_killed) 
        { 
            is_killed = _is_killed; 
        }

        time_t getGlobalStartTime()
        {
            return global_start_time;
        }

        time_t getNetworkOverhead()
        {
            return network_overhead;
        }
        void setNetworkOverhead(time_t _network_overhead)
        {
            network_overhead = _network_overhead;
        }
};

class SimpleMonitor : public Monitor
{
    private:
        time_t start_time;
        state current_state;
        pid_t current_pid;
        time_t module_time[MODULE_COUNT];
        TmpFile* cur_tmp_stdout;
        TmpFile* cur_tmp_stderr;
    public:
        SimpleMonitor(std::string checker_name, time_t _global_start_time);
        ~SimpleMonitor() {}

        state getCurrentState(unsigned int thread_index = 0) 
        { 
            return current_state; 
        }

        void setState(state _state, time_t _start_time, 
                unsigned int thread_index = 0)
        {
            current_state = _state;
            start_time = _start_time;
        }

        void setPID(pid_t _pid, unsigned int thread_index = 0)
        {
            current_pid = _pid;
        }

        void addTime(time_t end_time, unsigned int thread_index = 0);
          
        std::string getStats(time_t global_time = 0);
            
        void handleSIGKILL();
        void handleSIGALARM();
 
        void setTmpFiles(TmpFile* tmp_stdout, TmpFile* tmp_stderr);
        void removeTmpFiles();
};

class ParallelMonitor : public Monitor
{
    private:
        unsigned int thread_num;
            
        state* current_state;
        pid_t* current_pid;
        bool* alarm_killed;

        time_t* checker_start_time;
        time_t* stp_start_time;
        time_t tracer_start_time;

        std::set<interval> checker_time;
        std::set<interval> stp_time;
        time_t tracer_time;
        time_t checker_alarm;
        time_t tracer_alarm;

        pthread_mutex_t add_time_mutex;

        std::vector<std::pair<TmpFile*, TmpFile*> > tmp_files;
    public:
        ParallelMonitor(std::string checker_name, 
                        time_t _global_start_time, unsigned int _thread_num);
        ~ParallelMonitor();

        void setAlarm(time_t _checker_alarm, time_t _tracer_alarm)
        {
          checker_alarm = _checker_alarm;
          tracer_alarm = _tracer_alarm;
        }

        bool getAlarmKilled(unsigned int thread_index = 0) 
        { 
            return alarm_killed[thread_index - 1]; 
        }

        void setState(state _state, time_t _start_time, 
                      unsigned int thread_index = 0);

        void setPID(pid_t _pid, unsigned int thread_index = 0)
        {
            current_pid[thread_index] = _pid;
        }
            
        void addTime(time_t end_time, unsigned int thread_index = 0);
           
        std::string getStats(time_t global_time = 0);
             
        state getCurrentState(unsigned int thread_index = 0) 
        { 
            return current_state[thread_index]; 
        }

        void handleSIGALARM();

        void handleSIGKILL();

        void setTmpFiles(TmpFile* tmp_stdout, TmpFile* tmp_stderr);
        void removeTmpFiles();
};
 
#endif
