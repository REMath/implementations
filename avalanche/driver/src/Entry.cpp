/*---------------------------------------------------------------------------*/
/*------------------------------ AVALANCHE ----------------------------------*/
/*- Driver. Coordinates other processes, traverses conditional jumps tree. --*/
/*------------------------------ Entry.cpp ----------------------------------*/
/*---------------------------------------------------------------------------*/

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

#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <string>
#include <set>
#include <signal.h>
#include <dirent.h>

#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <cstdlib>
#include <string.h>
#include <cerrno>
#include <fstream>

#include "ExecutionManager.h"
#include "Logger.h"
#include "OptionConfig.h"
#include "OptionParser.h"
#include "Input.h"
#include "Error.h"
#include "Thread.h"
#include "Monitor.h"

using namespace std;

static Logger *logger = Logger::getLogger();
Monitor* monitor;

ExecutionManager* em;
OptionParser *op;

extern Thread remote_thread;
extern PoolThread *threads;
extern Input* initial;
extern vector<Error*> report;

extern int in_thread_creation;

int thread_num;
extern int dist_fd;

OptionConfig* opt_config;

void cleanUp()
{
    monitor->removeTmpFiles();
    string dir_name = ExecutionManager::getTempDir();
    if (thread_num > 0)
    {
        for (int i = 1; i < thread_num + 1; i ++)
        {
            ostringstream file_modifier;
            file_modifier << "_" << i;
            string modifier_log = file_modifier.str() + string(".log");
            unlink((dir_name + string("basic_blocks") + modifier_log).c_str());
            unlink((dir_name + string("execution") + modifier_log).c_str());
            unlink((dir_name + string("curtrace") + modifier_log).c_str());
            unlink((dir_name + string("replace_data") + modifier_log).c_str());
            unlink((dir_name + string("argv.log") + modifier_log).c_str());
            for (int j = 0; j < opt_config->getNumberOfFiles(); j ++)
            {
                unlink((opt_config->getFile(j) + file_modifier.str()).c_str());
            }
        }
        delete []threads;
    }
    if (opt_config->enabledCleanUp()) {
        unlink((dir_name + string("basic_blocks.log")).c_str());
        unlink((dir_name + string("curtrace.log")).c_str());
        unlink((dir_name + string("curdtrace.log")).c_str());
        unlink((dir_name + string("execution.log")).c_str());
        unlink((dir_name + string("prediction.log")).c_str());
        unlink((dir_name + string("dangertrace.log")).c_str());
        unlink((dir_name + string("trace.log")).c_str());
        unlink((dir_name + string("actual.log")).c_str());
        unlink((dir_name + string("divergence.log")).c_str());
        unlink((dir_name + string("replace_data")).c_str());
        unlink((dir_name + string("offsets.log")).c_str());
        if (opt_config->getCheckArgv() != "")
        {
            unlink((dir_name + string("argv.log")).c_str());
            unlink((dir_name + string("arg_lengths")).c_str());
        }
        if (dir_name != "")
        {
            if (rmdir(dir_name.substr(0, dir_name.length() - 1).c_str()) < 0)
            {
                if (errno != EEXIST)
                {
                    LOG(Logger::ERROR, "Cannot delete temporary directory " <<
                                       dir_name << " : " << strerror(errno));
                }
            }
        }
    }
    for (int i = 0; i < report.size(); i ++)
    {
        delete (report.at(i));
    }
    delete em;
    delete op;
    delete opt_config;
    delete initial;
    delete monitor;
    delete logger;
}

void reportResults()
{
    // Exploits report

    bool to_file = (opt_config -> getReportLog() != string (""));
    ofstream report_f;

    if (to_file)
    {
        report_f.open((opt_config->getResultDir() + 
                        opt_config->getReportLog()).c_str());
        if (report_f.bad())
        {
          to_file = false;
        }
    }

    if (!to_file)
    {
        LOG(Logger::REPORT, "Unique error(s) found: " << 
                            report.size () << ".");
    }

    if (report.size() > 0)
    {
        for (int i = 0; i < report.size(); i++)
        {
            string summary = 
                report.at(i)->getSummary(opt_config->getPrefix(),
                                         opt_config->getNumberOfFiles(),false);
            if (to_file)
            {
                report_f << summary;
            }
            else
            {
                LOG(Logger::REPORT, summary);
            }
        }
    }

    ofstream error_f((opt_config->getResultDir() + "error_list.log").c_str());
    if (error_f.bad())
    {
        LOG(Logger::ERROR, 
                "Error opening file " << opt_config->getResultDir() <<
                "error_list.log: " << strerror(errno));
    }
    else
    {
        for (int i = 0; i < report.size(); i ++)
        {
            error_f << report[i]->getList();
        }
        error_f.close();
    }

    // Time statistics

    time_t end_time = time(NULL);
    LOG (Logger::REPORT, endl << "Time statistics: " << 
        end_time - monitor->getGlobalStartTime() << " sec, " << 
        monitor->getStats(end_time - monitor->getGlobalStartTime() - 
                                     monitor->getNetworkOverhead()));
    LOG(Logger::REPORT, "");
}

void sig_hndlr(int signo)
{
    if (opt_config->getDistributed())
    {
        write(dist_fd, "q", 1);
        shutdown(dist_fd, SHUT_RDWR);
        close(dist_fd);
    }
    if (!(opt_config->usingSockets()) && 
        !(opt_config->usingDatagrams()) &&
        (initial != NULL))
    {
        initial->dumpFiles();
    }
    monitor->setKilledStatus(true);
    monitor->handleSIGKILL();
    for (int i = 0; i < thread_num; i ++)
    {
        if (in_thread_creation != i)
        {
            threads[i].waitForThread();
        }
    }
/*    if ((thread_num > 0) && opt_config->getRemoteValgrind())
    {
        pthread_cancel(remote_thread.getTID());
        remote_thread.waitForThread();
    }*/
    reportResults();
    cleanUp();
    exit(0);
}

int main(int argc, char *argv[])
{
    time_t start_time = time(NULL); 
    signal(SIGINT, sig_hndlr);
    signal(SIGPIPE, SIG_IGN);
    op = new OptionParser(argc, argv);
    opt_config = op->run();
        
    if (opt_config == NULL || opt_config->empty()) 
    {
        LOG(Logger::JOURNAL, 
                "Use 'avalanche --help' for a complete options list.");
        return EXIT_FAILURE;
    }

    if (opt_config -> getVerbose ()) logger -> setVerbose ();
    if (opt_config -> getDebug ()) logger -> setDebug ();
    if (opt_config -> getProgramOutput ()) logger -> setProgramOutput ();
    if (opt_config -> getNetworkLog ()) logger -> setNetworkLog ();

    thread_num = opt_config->getSTPThreads();
    string checker_name = (opt_config->getPlugin());
    if (thread_num > 0)
    {
        monitor = new ParallelMonitor(checker_name, start_time, thread_num);
        ((ParallelMonitor*)monitor)->setAlarm(opt_config->getAlarm(), 
                                              opt_config->getTracegrindAlarm());
        threads = new PoolThread[thread_num];
    }
    else
    {
        monitor = new SimpleMonitor(checker_name, start_time);
    }
    checker_name.clear();
    Error::initCounters();
    LOG_TIME (Logger :: VERBOSE, "Avalanche, a dynamic analysis tool.");

    if (opt_config->getResultDir() != string(""))
    {
        if (mkdir(opt_config->getResultDir().c_str(), 
                  S_IRWXG | S_IRWXO | S_IRWXU) < 0)
        {
            if (errno != EEXIST)
            {
                LOG(Logger::ERROR, 
                        "Cannot create directory " << 
                        opt_config->getResultDir() << ": " << strerror(errno));
                opt_config->setResultDir("");
            }
        }
    }
    
    try
    {
        em = new ExecutionManager(opt_config);
        string temp_dir = ExecutionManager::getTempDir();
        em->run();
    }
    catch (char *msg)
    {
    }
    /* We need 2 separate try-catch blocks so that an attempt to restore
       initial input files is made. */
    try
    {
        if (!(opt_config->usingSockets()) && !(opt_config->usingDatagrams()))
        {
            initial->dumpFiles();
        }
    }
    catch (char *msg)
    {
        LOG(Logger::REPORT, "Warning! Input file(s) may not be restored to \
                             initial state!");
    }
    reportResults();
    cleanUp();
    return EXIT_SUCCESS;
}

