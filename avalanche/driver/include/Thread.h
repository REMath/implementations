/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*------------------------------------- Thread.h -----------------------------------------*/
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

#ifndef _THREAD_H
#define _THREAD_H

#include <pthread.h>
#include <iostream>
#include <map>
#include <string>

class Thread;

struct data_wrapper
{
  Thread* this_pointer;
  void* data;
};

struct job_wrapper
{
  void* (*work_func) (void*);
  void* data;
};

class Thread
{
  protected:
           std::map <std::string, void*> private_data;
           static std::map <std::string, void*> shared_data;
           pthread_t tid;
           int user_tid;
  public:
           Thread() : tid(0), user_tid(-1) {}
           Thread(pthread_t _tid, int _user_tid) : tid(_tid), user_tid(_user_tid) {}
           ~Thread() {}

           int createThread(void* data, bool is_joinable = true);
           virtual void waitForThread();
           
           static void* createAndRun(void* input);

           virtual void doWork(void* data);
           
           void addPrivateData(void* _data_unit, std::string name) 
           { 
             private_data[name] = _data_unit; 
           }
           void clearPrivateData() 
           { 
             private_data.clear(); 
           }
           void* getPrivateData(std::string name) 
           { 
             return private_data[name]; 
           }
              
           static void addSharedData(void* _data_unit, std::string name)
           { 
             shared_data[name] = _data_unit;
           }
           static void clearSharedData() 
           { 
             shared_data.clear(); 
           }
           static void* getSharedData(std::string name) 
           { 
             return shared_data[name];
           }

           void printMessage(const char* message, bool show_real_tid = false);

           void setCustomTID(int _tid) 
           { 
             user_tid = _tid;  
           }

           int getCustomTID() 
           { 
             return user_tid; 
           }

           pthread_t getTID() 
           { 
             return tid; 
           }
};

class PoolThread : public Thread
{
  public:
           enum Status {UNINIT = -1, BUSY = 0, FREE = 1};
  private:
           pthread_mutex_t* work_finish_mutex;
           pthread_cond_t* work_finish_cond;
           int thread_status;
           int* active_threads;
  public:
           PoolThread() : work_finish_mutex(NULL), work_finish_cond(NULL), thread_status(-1), active_threads(NULL) {}
           ~PoolThread() {}

           void waitForThread()
           {
             if (thread_status != UNINIT)
             {
               Thread::waitForThread();
               thread_status = UNINIT;
             }
           }
           
           void setPoolSync(pthread_mutex_t* _mutex, pthread_cond_t* _cond, int* _active_threads)
           {
             work_finish_mutex = _mutex;
             work_finish_cond = _cond;
             active_threads = _active_threads;
           }
 
           int setStatus(int _status)
           {
             thread_status = _status;
           }
           
           int getStatus() 
           { 
             return thread_status;
           }
           void doWork(void* data);
};

#endif
