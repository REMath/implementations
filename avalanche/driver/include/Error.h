/*---------------------------------------------------------------------------*/
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

#ifndef __ERROR__H__
#define __ERROR__H__

#include <set>
#include <string>
#include <utility>

enum {
    KERNEL_SIGNAL,
    OWN_SIGNAL,
    OTHER_SIGNAL
};

enum {
    CRASH,
    MC_MEMORY,
    HG_THREAD,
    
    NO_CHECK
};

/* Do not change the order and append new errors to the end,
   or matching will break. */

enum {
    /* Exploits */
    CRASH_TERMINATED,   /* received terminating signal */
    CRASH_SIGALRM,      /* received SIGALRM */
    
    /* Memcheck error */
    MC_UNINIT,          /* Use of uninitialized byte(s) */
    MC_UNADDR,          /* Use of unaddressable byte(s) */
    MC_INVALID_R,       /* Invalid read */
    MC_INVALID_W,       /* Invalid write */
    MC_INVALID_FREE,    /* Invalid free */
    MC_INVALID_MEM,     /* Mismatched alloc/free */
    MC_OVERLAP,         /* Src and dst overlap */
    MC_DEF_LOST,        /* Definite leak */
    MC_POSS_LOST,       /* Possible leak */
    
    /* Helgrind error */
    HG_LOCK_ORDER,      /* Violated lock order */
    HG_PTHREAD_API,     /* pthread API error */
    HG_UNLOCK_INVALID,  /* Unlocked invalid lock */
    HG_UNLOCK_FOREIGN,  /* Unlocked foreign lock */
    HG_UNLOCK_UNLOCKED, /* Double unlock */
    HG_DATA_RACE,       /* Possible data race */
    
    UNKNOWN
};

struct errorInfo
{
    unsigned int error_code;
    const char* pattern;
};

class Error
{
protected:
    static int error_num;
    static int subtype_num[NO_CHECK];
    unsigned int id;
    std::string trace;
    std::set<int> inputs;
    std::string command;
    std::string all_command;
    std::string trace_file;
    int type;
    int status;
public:
    Error(int _type, int _status);
    ~Error() {}

    std::string getSummary(std::string prefix, int input_num, bool verbose);
    std::string getList();

    void setCommand(std::string _command);
    void updateCommand(std::string _command);
    std::string getCommand();

    void setTrace(std::string _trace);
    std::string getTrace();
    std::string getTraceBody();
    std::string getTraceHeader();
    
    int getSubtypeNumber();
    void incSubtypeNumber();
    
    std::string getShortName();
    std::string getFileNameModifier();
    
    void setStatus(int _status);
    int getStatus();
    
    int getType();
        
    void setTraceFile(std::string _trace_file);
    std::string getTraceFile();
    
    void addInput(int input);
    
    static void initCounters();
    
    static char* match(char* source, errorInfo &result, int filter);
    static Error* create(unsigned int error_code);
    
    static std::pair<int, int> getFilterLimits(int filter);
    static int getFilterCode(std::string plugin_name);
};

#endif

