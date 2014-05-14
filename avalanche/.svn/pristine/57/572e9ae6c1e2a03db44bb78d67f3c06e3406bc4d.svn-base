/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*---------------------------------- OptionConfig.h --------------------------------------*/
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

#ifndef __OPTION_CONFIG__H__
#define __OPTION_CONFIG__H__

#include <cstddef>
#include <vector>
#include <string>


class OptionConfig
{
public:
    OptionConfig(): reportLog(std::string("")),
                    debug(false),
                    protectMainAgent(false),
                    STPThreadsAuto(false),
                    checkDanger(false),
                    verbose (false),
                    programOutput (false),
                    networkLog (false),
                    sockets(false),
                    traceChildren(false),
                    sizeOfLong(sizeof(long)),
                    datagrams(false),
                    distributed(false), 
                    agent(false), 
                    suppressSubcalls(false),
                    dumpCalls(false),
                    leaks(false),
                    protectArgName(false),
                    cleanUp(true),
                    funcFilterFile(std::string("")),
                    depth(100),
                    startdepth(1),
                    alarm(300),
                    tracegrindAlarm(0),
                    plugin(std::string("covgrind")),
                    host(std::string("")),
                    prefix(std::string("")),
                    distHost(std::string("127.0.0.1")),
                    remoteHost(std::string("127.0.0.1")),
                    remoteValgrind(std::string("")),
                    port(65536),
                    distPort(65536),
                    remotePort(65536),
                    STPThreads(0),
                    checkArgv(std::string("")),
                    resultDir(std::string("")),
                    agentDir(std::string("")),
                    valgrindPath(std::string(""))
    {}

    OptionConfig(const OptionConfig *opt_config)
    {
        reportLog       = opt_config->reportLog;
        traceChildren   = opt_config->traceChildren;
        debug           = opt_config->debug;
        protectMainAgent= opt_config->protectMainAgent;
        distributed     = opt_config->distributed;
        agent           = opt_config->agent;
        checkDanger     = opt_config->checkDanger;
        verbose         = opt_config->verbose;
        programOutput   = opt_config->programOutput;
        networkLog      = opt_config->networkLog;
        sockets         = opt_config->sockets;
        datagrams       = opt_config->datagrams;
        depth           = opt_config->depth;
        startdepth      = opt_config->startdepth;
        valgrind        = opt_config->valgrind;
        prog_and_arg    = opt_config->prog_and_arg;
        files           = opt_config->files;
        alarm           = opt_config->alarm;
        tracegrindAlarm = opt_config->tracegrindAlarm;
        host            = opt_config->host;
        port            = opt_config->port;
        distHost        = opt_config->distHost;
        distPort        = opt_config->distPort;
        remoteHost      = opt_config->remoteHost;
        remotePort      = opt_config->remotePort;
        remoteValgrind  = opt_config->remoteValgrind;
        leaks           = opt_config->leaks;
        funcFilterFile  = opt_config->funcFilterFile;
        funcFilterUnits = opt_config->funcFilterUnits;
        suppressSubcalls= opt_config->suppressSubcalls;
        dumpCalls       = opt_config->dumpCalls;
        inputFilterFile = opt_config->inputFilterFile;
        STPThreads      = opt_config->STPThreads;
        STPThreadsAuto	= opt_config->STPThreadsAuto;
        plugin          = opt_config->plugin;
        prefix          = opt_config->prefix;
        checkArgv       = opt_config->checkArgv;
        protectArgName  = opt_config->protectArgName;
        sizeOfLong      = opt_config->sizeOfLong;
        cleanUp         = opt_config->cleanUp;
        resultDir       = opt_config->resultDir;
        agentDir        = opt_config->agentDir;
        valgrindPath    = opt_config->valgrindPath;
    }

    bool empty() const
    { return prog_and_arg.empty(); }

    void setValgrind(const std::string &dir)
    { valgrind = dir; }
    
    const std::string &getValgrind() const
    { return valgrind; }

    void setFuncFilterFile(const std::string &fileName)
    { funcFilterFile = fileName; }
    
    const std::string getFuncFilterFile() const
    { return funcFilterFile; }

    void setInputFilterFile(const std::string &fileName)
    { inputFilterFile = fileName; }
    
    const std::string getInputFilterFile() const
    { return inputFilterFile; }

    const std::string getReportLog() const
    { return reportLog; }
    
    std::string getRemoteHost()
    { return remoteHost; }

    void setRemoteHost(std::string& host)
    { remoteHost = host; }

    void setReportLog(std::string reportLog)
    { this->reportLog = reportLog; }

    const std::string getResultDir() const
    { return resultDir; }

    void setResultDir(std::string resultDir)
    { this->resultDir = resultDir; }

    const std::string getAgentDir() const
    { return agentDir; }

    void setAgentDir(std::string agentDir)
    { this->agentDir = agentDir; }

    const std::string getPlugin() const
    { return plugin; }

    void setPlugin(std::string plugin)
    { this->plugin = plugin; }

    const std::string getValgrindPath() const
    { return valgrindPath; }

    void setValgrindPath(std::string valgrindPath)
    { this->valgrindPath = valgrindPath; }

    void setDebug()
    { debug = true; }
    
    bool getDebug() const
    { return debug; }

    int getSizeOfLong() const
    { return sizeOfLong; }

    void setSizeOfLong(int size)
    { sizeOfLong = size; }

    void setProtectArgName()
    { protectArgName = true; }
    
    bool getProtectArgName() const
    { return protectArgName; }

    void setSTPThreadsAuto()
    { STPThreadsAuto = true; }
    
    bool getSTPThreadsAuto() const
    { return STPThreadsAuto; }

    void setTraceChildren()
    { traceChildren = true; }
    
    bool getTraceChildren() const
    { return traceChildren; }

    void setProtectMainAgent()
    { protectMainAgent = true; }

    bool getProtectMainAgent() const
    { return protectMainAgent; }

    void setCheckArgv(const std::string &arg)
    { checkArgv = arg; }

    std::string getCheckArgv() const
    { return checkArgv; }

    void setDumpCalls()
    { dumpCalls = true; }

    bool getDumpCalls() const
    { return dumpCalls; }

    bool getSuppressSubcalls() const
    { return suppressSubcalls; }

    void setSuppressSubcalls()
    { suppressSubcalls = true; }
     
    void setVerbose()
    { verbose = true; }

    bool getVerbose()
    { return verbose; }
    
    void setProgramOutput()
    { programOutput = true; }

    bool getProgramOutput()
    { return programOutput; }
    
    void setNetworkLog()
    { networkLog = true; }

    bool getNetworkLog ()
    { return networkLog; }
    
    void setDistributed()
    { distributed = true; }
    
    bool getDistributed() const
    { return distributed; }

    void setAgent()
    { agent = true; }

    void setNotAgent()
    { agent = false; }
    
    bool getAgent() const
    { return agent; }

    void setSTPThreads(int num)
    { STPThreads = num; }
    
    int getSTPThreads() const
    { return STPThreads; }

    void setStartdepth(int startdepth)
    { this->startdepth = startdepth; }
    
    int getStartdepth() const
    { return startdepth; }

    void setCheckDanger()
    { checkDanger = true; }
    
    bool getCheckDanger() const
    { return checkDanger; }
    
    void disableCleanUp()
    { cleanUp = false; }
    
    bool enabledCleanUp()
    { return cleanUp; }

    void setUsingSockets()
    { sockets = true; }
    
    bool usingSockets() const
    { return sockets; }

    void setUsingDatagrams()
    { datagrams = true; }
    
    bool usingDatagrams() const
    { return datagrams; }

    void setLeaks()
    { leaks = true; }
    
    bool checkForLeaks() const
    { return leaks; }

    void setDepth(std::size_t max_depth)
    { depth = max_depth; }

    std::size_t getDepth() const
    { return depth; }

    void setAlarm(unsigned int alarm)
    { this->alarm = alarm; }

    unsigned int getAlarm() const
    { return alarm; }

    void addFuncFilterUnit(const std::string &fn)
    { funcFilterUnits.push_back(fn); }

    const std::vector<std::string> getfuncFilterUnits() const
    { return funcFilterUnits; }
  
    std::string getFuncFilterUnit(int i)
    { return funcFilterUnits.at(i); }

    int getFuncFilterUnitsNum()
    { return funcFilterUnits.size(); }

    void setTracegrindAlarm(unsigned int alarm)
    { this->tracegrindAlarm = alarm; }

    unsigned int getTracegrindAlarm() const
    { return tracegrindAlarm; }

    void setPort(unsigned int port)
    { this->port = port; }

    unsigned int getPort() const
    { return port; }

    void setDistPort(unsigned int port)
    { distPort = port; }

    unsigned int getDistPort() const
    { return distPort; }

    void setRemotePort(unsigned int port) 
    { remotePort = port; }

    unsigned int getRemotePort() const
    { return remotePort; }

    void addProgAndArg(const std::string &arg)
    { prog_and_arg.push_back(arg); }

    const std::vector<std::string> &getProgAndArg() const
    { return prog_and_arg; }
  
    std::string getFile(int i)
    { return files.at(i); }

    int getNumberOfFiles()
    { return files.size(); }

    void addFile(std::string& filename)
    { files.push_back(filename); }

    std::string getHost()
    { return host; }

    void setHost(std::string& host)
    { this->host = host; }

    std::string getDistHost()
    { return distHost; }

    void setDistHost(std::string& host)
    { distHost = host; }

    std::string getPrefix()
    { return prefix; }

    void setPrefix(std::string& prefix)
    { this->prefix = prefix; }

    void setRemoteValgrind(std::string& type)
    { remoteValgrind = type; }
    
    std::string getRemoteValgrind() const
    { return remoteValgrind; }


private:
    /* Enable DEBUG logging level.
       Disabled by default (false). */
    bool                     debug;

    /* Enable minimum limit for number of inputs in main avalanche:
         no inputs are given to agents as long as there are more than
         5 * number_of_agents.
       Disabled by default (false). */
    bool                     protectMainAgent;

    /* Enable VERBOSE logging level.
       Disabled by default (false). */
    bool                     verbose;

    /* Enable PROGRAM_OUTPUT logging level.
       Disabled by default (false). */
    bool                     programOutput;

    /* Enable NETWORK logging level.
       Disabled by default (false). */
    bool                     networkLog;

    /* Set avalanche to trace data from TCP sockets.
       Not set by default (false). */
    bool                    sockets;

    /* Set avalanche to trace data from UDP sockets.
       Not set by default (false). */
    bool                     datagrams;

    /* Enable dangertrace.log parsing.
       Disabled by default (false). */
    bool                     checkDanger;

    /* Add --check-leak=yes in memcheck options.
       Not used by default (false). */
    bool                     leaks;

    /* Enable ignoring QUERY's in nested calls during 
         separate function analysis.
       Disabled by default (false). */
    bool                     suppressSubcalls;

    /* Enable dumping names of functions containing QUERY's.
         Causes avalanche to run a single iteration, dumps calls
         in calldump.log.
       Disabled by default (false). */
    bool                     dumpCalls;

    /* Enable child processes analysis.
       Disabled by defualt (false). */
    bool                     traceChildren;

    /* Set avalanche to run in distributed mode.
       Not set by defualt (false). */
    bool                     distributed;

    /* Set avalanche to run in split mode.
       Not set by default ("").
       Use 'host' if remote plugin is a server;
       use 'client' if main avalanche is a server;*/
    std::string              remoteValgrind;

    /* Set avalanche to agent mode.
         Causes avalanche to request a knew input when all existing
         have score=0.
       Not set by defualt (false). */
    bool                     agent;

    /* Enable automatic detection of STP threads number.
       Not set by default (false). */
    bool                     STPThreadsAuto;

    /* Enable extra protection for command line arguments:
         for arguments starting with arg_name=arg_value only arg_value
         can be modified by avalanche.
       Disabled by default (false). */
    bool                     protectArgName;
    
    /* Enable removal of /tmp/avalanche-XXXXXX/ upon finishing the analysis.
       Enabled by default (true). */
    bool                     cleanUp;

    /* Valgrind plugin to check inputs for errors.
       Set to "covgrind" by default. */
    std::string              plugin;

    /* Path to folder to store exploits, memchecks, stacktraces and calldump. 
       Not set by default (""). */
    std::string              resultDir;

    /* Path to folder to store exploits, memchecks, stacktraces and calldump
         for av-agent. 
       Not set by default (""). */
    std::string              agentDir;
    
    /* Path to folder to store exploits, memchecks, stacktraces and calldump
         for plugin-agent.
       Not set by default (""). */
    std::string              reportLog;

    /* Path to file with list of function names for separate function analysis.
       Not set by default (""). */
    std::string              funcFilterFile;

    /* Maximum depth (number of QUERY's) for tracegrind.
       Set to 100 by default. */
    std::size_t              depth;

    /* Path to valgrind binary.
       Set automatically. */
    std::string              valgrind;

    /* Path to analyzed executable and arguments.
       Not set by default. */
    std::vector<std::string> prog_and_arg;

    /* Input files to be considered tainted data source.
       Not set by default. */
    std::vector<std::string> files;

    /* Covgrind/memcheck timeout in seconds.
       Set to 300 by default. */
    unsigned int             alarm;

    /* Tracegrind timeout in seconds.
       Not set by default. */
    unsigned int             tracegrindAlarm;

    /* IPv4 address for network connection for --sockets/--datagrams.
       Not set by default. */
    std::string	             host;

    /* av-dist IPv4.
       Set to 127.0.0.1 by default. */
    std::string              distHost;

    /* plugin-agent IPv4.
       Set to 127.0.0.1 by default. */
    std::string              remoteHost;

    /* Port number for network connection for --sockets/datagrams.
       Set to 65536 by default. */
    unsigned int             port;

    /* av-dist port number.
       Set to 65536 by default. */
    unsigned int             distPort;

    /* plugin-agent port number.
       Set to 65536 by default. */
    unsigned int             remotePort;

    /* Function names to be used for separate function analysis.
       Not set by default. */
    std::vector<std::string> funcFilterUnits;

    /* Path to file containing mask for input filtering.
       Not set by default. */
    std::string              inputFilterFile;

    /* Prefix added to exploits, memchecks and stacktraces file names.
       Not set by default (""). */
    std::string              prefix;

    /* Initial depth (number of first QUERY to be used).
       Set to 1 by default. */
    unsigned int             startdepth;

    /* Number of STP threads.
       Not set by default (0). */
    unsigned int             STPThreads;

    /* String containing argument numbers (1,2,...) to be checked 
         as a source of tainted data.
       Not set by default (""). */
    std::string              checkArgv;

    /* Pointer size synchronization for split mode.
       Set automatically. */
    int                      sizeOfLong;

    std::string              valgrindPath;
};


#endif //__OPTION_CONFIG__H__

