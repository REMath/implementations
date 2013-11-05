/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*--------------------------------- OptionParser.cpp -------------------------------------*/
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

#include <unistd.h>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <arpa/inet.h>

#include "OptionParser.h"
#include "OptionConfig.h"
#include "Logger.h"

using namespace std;

static string supported_plugins[] = {
                "covgrind",
                "memcheck",
                "helgrind",
                ""
};

static bool distHostSpecified;
static bool distPortSpecified;
static Logger* logger = Logger::getLogger();

int parseArgvMask(const char* str, int argc, int* argFilterUnits);
long int isNumber(string number);

static void printHelpBanner()
{
    char banner[] =
        "usage: avalanche [options] prog-and-args\n\n"
        "  user options defined in [ ]:\n"
        "    --help                       Print help and exit\n"
        "    --use-memcheck               Use memcheck instead of covgrind\n"
        "    --use-helgrind               Use helgrind instead of covgrind\n"
        "    --leaks                      Check for memory leaks\n"
        "                                 (ignored if '--use-memcheck' isn't specified)\n"
        "    --verbose, -v                Printing information about iteration (depth, heuristic), exploits/memchecks\n"
        "                                 (time, output file)\n"
        "    --program-output             Show program output at logs\n"
        "    --network-log                Show network logs\n"
        "    --debug                      Save some debugging information - divergent inputs, etc.\n"
        "    --depth=<number>             The number of conditions collected during one run of tracegrind\n"
        "                                 (default is 100). May be used in the form '--depth=infinity',\n"
        "                                 which means that tracegrind should collect all conditions in the trace\n"
        "    --alarm=<number>             Timer value in seconds (for infinite loop recognition) (default is 300)\n"
        "    --filename=<input_file>      The path to the file with the input data for the application being tested\n"
        "    --trace-children             Run valgrind plugins with '--trace-children=yes' option\n"
        "    --check-danger               Emit special constraints for memory access operations\n"
        "                                 and divisions (slows down the analysis)\n"
        "    --dump-calls                 Dump the list of functions manipulating with tainted data to calldump.log\n"
        "    --func-name=<name>           The name of function that should be used for separate function analysis\n"
        "    --func-file=<name>           The path to the file with the list of functions that\n"
        "                                 should be used for separate function analysis\n"
        "    --mask=<mask_file>           The path to the file with input mask\n"
        "    --suppress-subcalls          Ignore conditions in a nested function calls during separate analysis\n"
        "    --stp-threads=<number>       The number of STP queries handled simultaneously. May be used in the form\n"
        "                                 '--stp-threads=auto'. In this case the number of CPU cores is taken.\n"
        "    --report-log=<filename>      Dump exploits report to the specified file\n"
        "    --result-dir=<dirname>       Store exploits and error list in directory <dirname>\n"
        "\n"
        "  special options for sockets:\n"
        "    --sockets                    Mark data read from TCP sockets as tainted\n"
        "    --host=<IPv4 address>        IP address of the network connection (for TCP sockets only)\n"
        "    --port=<number>              Port number of the network connection (for TCP sockets only)\n"
        "    --datagrams                  Mark data read from UDP sockets as tainted\n"
        "    --alarm=<number>             Timer for breaking infinite waitings in covgrind\n"
        "                                 or memcheck (not set by default)\n"
        "    --tracegrind-alarm=<number>  Timer for breaking infinite waitings in tracegrind (not set by default)\n"
        "\n"
        "  options for distributed Avalanche:\n"
        "    --distributed                Tell Avalanche that it should connect to distribution server\n"
        "                                 and run distributed analysis\n"
        "    --dist-host=<IPv4 address>   IP address of the distribution server (default is 127.0.0.1)\n"
        "    --dist-port=<number>         Port number of the distribution server (default is 12200)\n"
        "    --protect-main-agent         Do not send inputs to the remore agents, if the overall number\n"
        "                                 of inputs in the main agent do not exceed 5 * <number_of_agents>\n"
        "\n"
        " using remote valgrind agent:\n"
        "    --remote-valgrind=server     Connect to remote valgrind agent (host name is necessary in this case)\n"
        "    --remote-valgrind=client     Await incoming connection from valgrind agent (do not specify host name)\n"
        "    --remote-host=<IPv4 address> IP address of the remote agent\n"
        "    --remote-port=<number>       Port number for connection wit remote agent\n";


    LOG(Logger::JOURNAL, banner);
}

OptionParser::OptionParser(int argc, char *argv[])
{
    setProgName(argv[0]);
    for (int i = 1; i < argc; i++)
        args.push_back(string(argv[i]));
}

OptionConfig *OptionParser::run() const
{
    OptionConfig *config = new OptionConfig;
    bool stpThreadsSpecified = false;
    distHostSpecified = false;
    distPortSpecified = false;
    bool fileSpecified = false;
    size_t sl = progName.find_last_of('/');
    size_t progArgc = 0;
    if (sl != string::npos) {
        config->setValgrind(progName.substr(0, sl + 1));
        config->setValgrindPath(string("../lib/avalanche/valgrind"));
    }
    else {
        config->setValgrind("");
    }

    for (size_t i = 0; i < args.size(); i++) {
        if (args[i].find("--filename=") != string::npos) {
            string filename = args[i].substr(strlen("--filename="));
            config->addFile(filename);
            fileSpecified = true;
        }
        else if (args[i].find("--host=") != string::npos) {
            string host = args[i].substr(strlen("--host="));
            struct in_addr p;
            if (inet_pton(AF_INET, host.c_str(), &p) == 0) {
                delete config;
                LOG(Logger::ERROR, "invalid '--host=' parameter");
                return NULL;
            }
            config->setHost(host);
        }
        else if (args[i].find("--dist-host=") != string::npos) {
            distHostSpecified = true;
            string host = args[i].substr(strlen("--dist-host="));
            struct in_addr p;
            if (inet_pton(AF_INET, host.c_str(), &p) == 0) {
                delete config;
                LOG(Logger::ERROR, "invalid '--dist-host=' parameter");
                return NULL;
            }
            config->setDistHost(host);
        }
        else if (args[i].find("--remote-host=") != string::npos) {
            string host = args[i].substr(strlen("--remote-host="));
            struct in_addr p;
            if (inet_pton(AF_INET, host.c_str(), &p) == 0) {
                delete config;
                LOG(Logger::ERROR, "invalid '--remote-host=' parameter");
                return NULL;
            }
            config->setRemoteHost(host);
        }
        else if (args[i].find("--report-log=") != string::npos) {
            string log = args[i].substr(strlen("--report-log="));
            config->setReportLog(log);
        }
        else if (args[i].find("--prefix=") != string::npos) {
            string prefix = args[i].substr(strlen("--prefix="));
            config->setPrefix(prefix);
        }
        else if (args[i].find("--depth=") != string::npos) {
            string depth = args[i].substr(strlen("--depth="));
            if (depth == string("infinity")) {
                config->setDepth(0);
            }
            else {
                if (isNumber(depth) == -1) {
                    delete config;
                    LOG(Logger::ERROR, "invalid '--depth' parameter.");
                    return NULL;
                }
                config->setDepth(atoi(depth.c_str()));
            }
        }
        else if (args[i].find("--startdepth=") != string::npos) {
            string depth = args[i].substr(strlen("--startdepth="));
            config->setStartdepth(atoi(depth.c_str()));
        }
        else if (args[i].find("--alarm=") != string::npos) {
            string alarm = args[i].substr(strlen("--alarm="));
            if (isNumber(alarm) == -1) {
                delete config;
                LOG(Logger::ERROR, "invalid '--alarm' parameter.");
                return NULL;
            }
            config->setAlarm(atoi(alarm.c_str()));
        }
        else if (args[i].find("--func-name=") != string::npos) {
            string name = args[i].substr(strlen("--func-name="));
            config->addFuncFilterUnit(name);
        }
        else if (args[i].find("--func-file=") != string::npos) {
            string fname = args[i].substr(strlen("--func-file="));
            config->setFuncFilterFile(fname);
        }
        else if (args[i].find("--mask=") != string::npos) {
            string fname = args[i].substr(strlen("--mask="));
            config->setInputFilterFile(fname);
        }
        else if (args[i].find("--tracegrind-alarm=") != string::npos) {
            string alarm = args[i].substr(strlen("--tracegrind-alarm="));
            if (isNumber(alarm) == -1) {
                delete config;
                LOG(Logger::ERROR, "invalid '--tracegrind-alarm' parameter.");
                return NULL;
            }
            config->setTracegrindAlarm(atoi(alarm.c_str()));
        }
        else if (args[i].find("--port=") != string::npos) {
            string port = args[i].substr(strlen("--port="));
            if (isNumber(port) == -1 || isNumber(port) > 65535) {
                delete config;
                LOG(Logger::ERROR, "invalid '--port' parameter.");
                return NULL;
            }
            config->setPort(atoi(port.c_str()));
        }
        else if (args[i].find("--dist-port=") != string::npos) {
            distPortSpecified = true;
            string port = args[i].substr(strlen("--dist-port="));
            if (isNumber(port) == -1 || isNumber(port) > 65535) {
                delete config;
                LOG(Logger::ERROR, "invalid '--dist-port' parameter.");
                return NULL;
            }
            config->setDistPort(atoi(port.c_str()));
        }
        else if (args[i].find("--valgrind-path=") != string::npos) {
            config->setValgrindPath(args[i].substr(strlen("--valgrind-path=")));
        }
        else if (args[i].find("--remote-port=") != string::npos) {
            string port = args[i].substr(strlen("--remote-port="));
            if (isNumber(port) == -1 || isNumber(port) > 65535) {
                delete config;
                LOG(Logger::ERROR, "invalid '--remote-port' parameter.");
                return NULL;
            }
            config->setRemotePort(atoi(port.c_str()));
        }
        else if (args[i].find("--stp-threads=") != string::npos) {
            string thread_num = args[i].substr(strlen("--stp-threads="));
            if (thread_num == string("auto")) {
                config->setSTPThreadsAuto();
                config->setSTPThreads(sysconf(_SC_NPROCESSORS_ONLN));
            }
            else {
                stpThreadsSpecified = true;
                config->setSTPThreads(atoi(thread_num.c_str()));
            }
        }
        else if (args[i].find("--check-argv=") != string::npos) {
            string argv_mask = args[i].substr(strlen("--check-argv="));
            config->setCheckArgv(argv_mask);
        }
        else if (args[i].find("--cleanup=") != string::npos) {
            if (args[i].substr(strlen("--cleanup=")) == "no") {
                config->disableCleanUp();
            }
        }
        else if (args[i].find("--remote-valgrind=") != string::npos) {
            string remote_vg_role = args[i].substr(strlen("--remote-valgrind="));
            if ((remote_vg_role != "host") && (remote_vg_role != "client"))
            {
                LOG(Logger::ERROR, "Only 'host' and 'client' options"
                                    " are available for --remote-valgrind");
                return NULL;
            }
            config->setRemoteValgrind(remote_vg_role);
        }
        else if (args[i].find("--result-dir=") != string::npos) {
            string result_dir = args[i];
            if (result_dir.size() > 0)
            {
                if (result_dir[result_dir.size() - 1] != '/')
                {
                        result_dir.push_back('/');
                }
            }
            config->setResultDir(result_dir.substr(strlen("--result-dir=")));
        }
        else if (args[i].find("--agent-dir=") != string::npos) {
            string agent_dir = args[i];
            if (agent_dir.size() > 0)
            {
                if (agent_dir[agent_dir.size() - 1] != '/')
                {
                        agent_dir.push_back('/');
                }
            }
            config->setAgentDir(agent_dir.substr(strlen("--agent-dir=")));
        }
        else if (args[i].find("--tool=") != string::npos) {
            string plugin_name = args[i].substr(strlen("--tool="));
            if (!checkSupportedPlugins(plugin_name))
            {
                LOG(Logger::ERROR, "Plugin \'" << plugin_name << "\' is not supported");
                return NULL;
            }
            config->setPlugin(plugin_name);
        }
        else if (args[i] == "--debug") {
            config->setDebug();
        }
        else if (args[i] == "--protect-arg-name") {
            config->setProtectArgName();
        }
        else if (args[i] == "--protect-main-agent") {
            config->setProtectMainAgent();
        }
        else if (args[i] == "--distributed") {
            config->setDistributed();
        }
        else if (args[i] == "--agent") {
            config->setAgent();
        }
        else if (args[i] == "--check-danger") {
            config->setCheckDanger();
        }
        else if (args[i] == "--trace-children") {
            config->setTraceChildren();
        }
        else if (args[i] == "--suppress-subcalls") {
            config->setSuppressSubcalls();
        }
        else if (args[i] == "--dump-calls") {
            config->setDumpCalls();
        }

        // Verbose options

        else if (args [i] == "--verbose" || args [i] == "-v") {
            config->setVerbose ();
        }
        else if (args[i] == "--program-output") {
            config->setProgramOutput ();
        }
        else if (args[i] == "--network-log") {
            config->setNetworkLog ();
        }
        else if (args[i] == "--use-helgrind") {
            config->setPlugin("helgrind");
        }
        else if (args[i] == "--leaks") {
            config->setLeaks();
        }
        else if (args[i] == "--sockets") {
            config->setUsingSockets();
        }
        else if (args[i] == "--datagrams") {
            config->setUsingDatagrams();
        }
        else if (args[i] == "--help") {
            printHelpBanner();
            delete config;
            return NULL;
        }
        else {
            // Program name and arguments

            config->addProgAndArg(args[i]);
            size_t j;
            for (j = i + 1; j < args.size(); j++)
            {
                config->addProgAndArg(args[j]);
            }
            progArgc = j - i;
            break;
        }
    }
        if (config->getAgent() && config->getDistributed()) {
        delete config;
        LOG(Logger::ERROR, "you cannot specify '--agent' and '--distributed' at the same time");
    }

    if ((config->getPlugin() != "covgrind") && config->getDumpCalls()) {
        delete config;
        LOG(Logger::ERROR, "'--dump-calls' can only be used with covgrind");
        return NULL;
    }

    if (!fileSpecified && !config->usingSockets() && !config->usingDatagrams() && (config->getCheckArgv() == "")) {
        delete config;
        LOG(Logger::ERROR, "no input files or sockets specified and command line option checking is not enabled");
        return NULL;
    }
    else if (config->usingSockets() && ((config->getPort() == 65536) || (config->getHost() == ""))) {
        delete config;
        LOG(Logger::ERROR, "if '--sockets' option is specified, then IP host address and port number must be also provided");
        return NULL;
    }
    else if (fileSpecified && (config->usingSockets() || config->usingDatagrams())) {
        delete config;
        LOG(Logger::ERROR, "you cannot specify '--filename' and '--sockets' or '--datagrams' at the same time");
        return NULL;
    }
   /* else if (config->getRemoteValgrind() && (config->getSTPThreads() != 0)){
        delete config;
        LOG(Logger::ERROR, "you cannot use remote valgrind plugin agent with STP parallelization enabled");
        return NULL;
    }*/
    else if (config->getCheckArgv() != "")
    {
        int* argFilterUnits = (int*) malloc((progArgc - 1) * sizeof(int));
    
        if (int error = parseArgvMask(config->getCheckArgv().c_str(), progArgc, argFilterUnits))
        {
            delete config;
            switch (error)
            {
                case 1: LOG(Logger::ERROR, "invalid '--check-argv' argument number."); break;
                case 2: LOG(Logger::ERROR, "duplicate '--check-argv' argument."); break;
                default: break;
            }
            free(argFilterUnits);
            return NULL;
        }

        for (int j = 0; j < config->getNumberOfFiles(); j++)
        {
            bool correspond = false;
            for (int i = 0; i < progArgc; i++)
            {
                if (config->getFile(j) == config->getProgAndArg().at(i))
                {
                    if (argFilterUnits[i - 1]) 
                    {
                        delete config;
                        LOG(Logger::ERROR, "you cannot specify '--filename' and '--check-argv' for the same files.");
                        return NULL;
                    }
                    correspond = true;
                }
            }
            if (!correspond)
            {
                LOG(Logger::ERROR, "file " + (config->getFile(j)) + " is not a program argument.");
                delete config;
                return NULL;
            }
        }
        free(argFilterUnits);
    }
    reportDummyOptions(config);
    return config;
}

void OptionParser::reportDummyOptions(OptionConfig* config) const
{
    vector <string> dummy_opts;
    if (((config->getHost() != "") || (config->getPort() != 65536)) && !config->usingSockets()) {
        string opt;
        if (config->getPort() != 65536) {
            opt.append(string("'--port' "));
        }
        if (config->getHost() != "") {
            opt.append(string("'--host' "));
        }
        dummy_opts.push_back(opt.append("(you should specify '--sockets')"));
    }
    if (config->getSuppressSubcalls() && (config->getFuncFilterFile() == "") && (config->getFuncFilterUnitsNum() == 0)) {
        dummy_opts.push_back(string("'--suppress-subcalls' (you should specify '--func-filter' or '--func-name')"));
    }
    if (config->checkForLeaks() && (config->getPlugin() != "memcheck")) {
        dummy_opts.push_back(string("'--leaks' (use '--tool=memcheck')"));
    }
    if ((distPortSpecified || distHostSpecified || config->getProtectMainAgent()) && !config->getDistributed()) {
        string opt;
        if (distPortSpecified) {
            opt.append(string("'--dist-port' "));
        }
        if (distHostSpecified) {
            opt.append(string("'--dist-host' "));
        }
        if (config->getProtectMainAgent()) {
            opt.append(string("'--protect-main-agent' "));
        }
        dummy_opts.push_back(opt.append("(use '--distributed')"));
    }
    if (dummy_opts.size()) {
        LOG(Logger::ERROR, "several options have no effect:");
        for (vector <string>::iterator i = dummy_opts.begin(); i != dummy_opts.end(); i ++) {
            LOG(Logger::ERROR, *i);
        }
    }
}

static string findInPath(const string &name)
{
    const char *var = getenv("PATH");
    if (var == NULL || var[0] == '\0') return string();

    string dirs = var;
    for (size_t beginPos = 0; beginPos < dirs.size(); ) {
        size_t colonPos = dirs.find(':', beginPos);
        size_t endPos = (colonPos == string::npos) ? dirs.size() : colonPos;
        string dir = dirs.substr(beginPos, endPos - beginPos);
        string fileName = dir + "/" + name;
        if (access(fileName.c_str(), X_OK) == 0) {
            return fileName;
        }
        beginPos = endPos + 1;
    }

    return string();
}

void OptionParser::setProgName(const string &path)
{
    if (path.find_last_of('/') == string::npos) {
        progName = findInPath(path);
    } else {
        progName = path;
    } 
}

// Parsing mask from "--check-argv" argument

int parseArgvMask (const char* str, int argc, int* argFilterUnits)
{
    for (int i = 0; i < argc - 1; i++)
    {
        argFilterUnits[i] = 0;
    }
    int i, curOffset = 0;
    char* curStr = (char*) malloc((strlen(str) + 1) * sizeof(char));
    char** endPtr = (char**) malloc(sizeof(char*));
    *endPtr = curStr;
    for (;;)
    {
        if (isspace(*str) || (*str == '\0'))
        {
            curStr[curOffset] = '\0';
            curOffset = 0;
            int index = strtol(curStr, endPtr, 10);
            if (index > argc - 1 || index <= 0)
            {
                return 1; // invalid argument number
            }
            if (*endPtr == curStr)
            {
                return 1;
            }
            if (argFilterUnits[index - 1]) return 2; // duplicate
            argFilterUnits[index - 1] = 1;
            if (*str == 0)
            {
                break;
            }
            str++;
        }
        else if (isdigit(*str))
        {
            curStr[curOffset++] = *(str++);
        }
        else
        {
            return 1; // is not digit
        }
    }
    free(endPtr);
    free(curStr);

    return 0;
}

// Determine whether a string is positive number

long int isNumber(string number)
{
    char* p;
    long int x = strtol(number.c_str(), &p, 10); 

    if ((p - number.c_str()) == number.length()) {
        if (x >= 0) return x;
        else return -1;
    }
    else return -1;
}

bool OptionParser::checkSupportedPlugins(string plugin_name) const
{
    int i = 0;
    while (supported_plugins[i] != "")
    {
        if (plugin_name == supported_plugins[i ++])
        {
            return true;
        }
    }
    return false;
}
