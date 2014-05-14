/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*------------------------------------ Thread.cpp ----------------------------------------*/
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

#include <signal.h>
#include <iostream>

#include "Thread.h"

using namespace std;

map <string, void*> Thread::shared_data;

int Thread::createThread(void* data, bool is_joinable)
{
    int ret_code;
    pthread_attr_t attr;
    data_wrapper* input = new data_wrapper;
    input->this_pointer = this;
    input->data = data;
    pthread_attr_init(&attr);
    if (is_joinable)
    {
        pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);
    }
    else
    {
        pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
    }
    ret_code = pthread_create(&tid, &attr, Thread::createAndRun, input);
    pthread_attr_destroy(&attr);
    return ret_code;
}

void* Thread::createAndRun(void* input)
{
    void* data = ((data_wrapper*) input)->data;
    Thread* this_pointer = ((data_wrapper*) input)->this_pointer;
    delete ((data_wrapper*)input);
    this_pointer->doWork(data);
}

void Thread::printMessage(const char* message, bool show_real_tid)
{
    cout << "thread #" << user_tid;
    if (show_real_tid)
    {
        cout << "(" << tid << ")";
    }
    cout << ": " << message << endl; 
}

void Thread::waitForThread()
{
    pthread_join(tid, NULL);
}

void Thread::doWork(void* data)
{
    sigset_t sigmask;
    sigemptyset(&sigmask);
    sigaddset(&sigmask, SIGINT);
    pthread_sigmask(SIG_BLOCK, &sigmask, NULL);
    (((job_wrapper*) data)->work_func) (((job_wrapper*) data)->data);
    pthread_exit(NULL);
}

void PoolThread::doWork(void* data)
{
    sigset_t sigmask;
    sigemptyset(&sigmask);
    sigaddset(&sigmask, SIGINT);
    pthread_sigmask(SIG_BLOCK, &sigmask, NULL);
    (((job_wrapper*) data)->work_func) (((job_wrapper*) data)->data);
    pthread_mutex_lock(work_finish_mutex);
    thread_status = FREE;
    (*active_threads) ++;
    pthread_cond_signal(work_finish_cond);
    pthread_mutex_unlock(work_finish_mutex);
    pthread_exit(NULL);
}
