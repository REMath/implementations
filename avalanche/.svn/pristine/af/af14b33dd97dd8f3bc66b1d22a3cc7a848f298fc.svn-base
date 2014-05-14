/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*------------------------------- ExecutionManager.cpp -----------------------------------*/
/*----------------------------------------------------------------------------------------*/

/*
   Copyright (C) 2009-2011 Ildar Isaev
      iisaev@ispras.ru
   Copyright (C) 2010-2011 Mikhail Ermakov
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


#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/wait.h>
#include <signal.h>
#include <stdio.h>
#include <errno.h>
#include <string>
#include <vector>
#include <set>
#include <cstring>
#include <stack>

#include "av_config.h" //for TMPDIR

#include "ExecutionManager.h"
#include "Logger.h"
#include "Error.h"
#include "OptionConfig.h"
#include "PluginExecutor.h"
#include "RemotePluginExecutor.h"
#include "STP_Executor.h"
#include "FileBuffer.h"
#include "ExecutionLogBuffer.h"
#include "SocketBuffer.h"
#include "Input.h"
#include "Thread.h"
#include "Monitor.h"

#define N 5

using namespace std;

extern Monitor* monitor;

PoolThread *threads;
Thread remote_thread;
extern int thread_num;

bool killed = false;
bool nokill = false;
bool f_error = false;

bool trace_kind;

static Logger *logger = Logger::getLogger();
Input* initial;
Kind kind;
bool is_distributed = false;

vector<Error*> report;

pthread_mutex_t add_inputs_mutex;
pthread_mutex_t add_exploits_mutex;
pthread_mutex_t add_bb_mutex;
pthread_mutex_t add_remote_mutex;
pthread_mutex_t finish_mutex;
pthread_cond_t finish_cond;
pthread_cond_t input_available_cond;

int in_thread_creation = -1;

int dist_fd;
int remote_fd;
int agents;

stack<pair<Input*, unsigned int> > remote_inputs;
bool launch_cv_stop;

static int connectTo(string host, unsigned int port)
{
  struct sockaddr_in st_socket_addr;
  int res, socket_fd;

  memset(&st_socket_addr, 0, sizeof(struct sockaddr_in));
 
  st_socket_addr.sin_family = AF_INET;
  st_socket_addr.sin_port = htons(port);
  res = inet_pton(AF_INET, host.c_str(), &st_socket_addr.sin_addr);
 
  if (res < 0)
  {
    perror("first parameter is not a valid address family");
    exit(EXIT_FAILURE);
  }
  else if (res == 0)
  {
    perror("second parameter does not contain valid ipaddress");
    exit(EXIT_FAILURE);
  }

   socket_fd = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
   if (socket_fd == -1)
   {
     perror("cannot create socket");
     exit(EXIT_FAILURE);
   }
   if (connect(socket_fd, (const struct sockaddr*)&st_socket_addr, sizeof(struct sockaddr_in)) < 0)
   {
     perror("connect failed");
     close(socket_fd);
     exit(EXIT_FAILURE);
   }
   return socket_fd;
}

int args_length;

#ifdef TMPDIR
static string temp_dir = string(TMPDIR);
#else
static string temp_dir = string("/tmp");
#endif

#define TMP_DIR_TEMPLATE_SIZE 6

static bool init_temp = false;

string ExecutionManager::getTempDir()
{
  if ((temp_dir.size() != 0) && !init_temp)
  {
    if (*(temp_dir.end() - 1) != '/')
    {
      temp_dir = temp_dir + string("/");
    }
    temp_dir = temp_dir + string("avalanche-");
    srand(time(NULL));
    for (int i = 0; i < TMP_DIR_TEMPLATE_SIZE; i ++)
    {
        ostringstream ss;
        ss << (char)('a' + rand() % ('z' - 'a'));
        temp_dir = temp_dir + ss.str();
    }
    temp_dir += '/';
    int res = mkdir(temp_dir.c_str(), S_IRWXU);
    if ((res == -1) && (errno != EEXIST))
    {
      LOG(Logger::ERROR, "Cannot create temp directory : " << strerror(errno));
      temp_dir = "";
    }
    init_temp = true;
  }
  return temp_dir;
}

ExecutionManager::ExecutionManager(OptionConfig *opt_config)
{
    config      = new OptionConfig(opt_config);
    cur_argv    = config->getProgAndArg();
    for (vector <string>::iterator i = cur_argv.begin() + 1; i != cur_argv.end(); i ++)
    {
        args_length += (*i).size();
    }
    args_length += cur_argv.size() - 2;
    divergences = 0;
    is_distributed = opt_config->getDistributed();
    if (thread_num > 0)
    {
        pthread_mutex_init(&add_inputs_mutex, NULL);
        pthread_mutex_init(&add_exploits_mutex, NULL);
        pthread_mutex_init(&add_bb_mutex, NULL);
        pthread_mutex_init(&finish_mutex, NULL);
        pthread_mutex_init(&add_remote_mutex, NULL);
        pthread_cond_init(&finish_cond, NULL);
        pthread_cond_init(&input_available_cond, NULL);
    }

    if (is_distributed)
    {
        dist_fd = connectTo(opt_config->getDistHost(), opt_config->getDistPort());
        LOG(Logger::NETWORK_LOG, "Connected to server.");
        write(dist_fd, "m", 1);
        read(dist_fd, &agents, sizeof(int));
    }
    if (opt_config->getRemoteValgrind() != "")
    {
        if (opt_config->getRemoteValgrind() == "host")
        {
            remote_fd = connectTo(opt_config->getRemoteHost(), opt_config->getRemotePort());
        }
        else
        {
            struct sockaddr_in st_socket_addr;
            int res, socket_fd;
            bool on;
            socket_fd = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
            setsockopt(socket_fd, SOL_SOCKET, SO_REUSEADDR, &on, sizeof(on));

            memset(&st_socket_addr, 0, sizeof(struct sockaddr_in));
            st_socket_addr.sin_family = AF_INET;
            st_socket_addr.sin_port = htons(config->getRemotePort());
            st_socket_addr.sin_addr.s_addr = INADDR_ANY;

            if(bind(socket_fd, (const struct sockaddr*)&st_socket_addr, sizeof(struct sockaddr_in)) < 0)
            {
                perror("bind failed");
                close(socket_fd);
                exit(EXIT_FAILURE);
            }

            if(listen(socket_fd, 10) < 0)
            {
                perror("listen failed");
                close(socket_fd);
                exit(EXIT_FAILURE);
            }

            remote_fd = accept(socket_fd, NULL, NULL);
            if (remote_fd < 0)
            {
                perror("accept failed");
                close(socket_fd);
                exit(EXIT_FAILURE);
            }
            close(socket_fd);
        }

        char buf[32];
        read(remote_fd, buf, strlen("avalanche"));
        buf[strlen("avalanche")] = '\0';
        if (strcmp(buf, "avalanche"))
        {
            LOG(Logger::ERROR, "Invalid authentication message from plugin-agent");
            throw "authentication";
        }
        int size;
        read(remote_fd, &size, sizeof(int));
        config->setSizeOfLong(size);
    }
}

void ExecutionManager::getTracegrindOptions(vector <string> &plugin_opts)
{
  ostringstream tg_invert_depth;
  if (temp_dir != "") 
  {
    if (config->getRemoteValgrind() != "")
    {
      plugin_opts.push_back(string("--host-temp-dir=") + temp_dir);
    }
    else
    {
      plugin_opts.push_back(string("--temp-dir=") + temp_dir);
    }
  }
  tg_invert_depth << "--invertdepth=" << config->getDepth();

  plugin_opts.push_back(tg_invert_depth.str());

  if (config->getDumpCalls())
  {
    plugin_opts.push_back(string("--dump-file=") + config->getResultDir() + 
                          string("calldump.log"));
  }
  else
  {
    plugin_opts.push_back("--dump-prediction=yes");
  }

  if (config->getCheckDanger())
  {
    plugin_opts.push_back(string("--check-danger=yes"));
  }
  if (config->getProtectArgName())
  {
    plugin_opts.push_back(string("--protect-arg-name=yes"));
  }

  for (int i = 0; i < config->getFuncFilterUnitsNum(); i++)
  {
    plugin_opts.push_back(string("--func-name=") + config->getFuncFilterUnit(i));
  }
  if (config->getFuncFilterFile() != "")
  {
    plugin_opts.push_back(string("--func-filter-file=") + config->getFuncFilterFile());
  }

  if (config->getInputFilterFile() != "")
  {
    plugin_opts.push_back(string("--mask=") + config->getInputFilterFile());
  }

  if (config->getSuppressSubcalls())
  {
    plugin_opts.push_back("--suppress-subcalls=yes");
  }

  if (config->usingSockets())
  {
    ostringstream tg_host;
    tg_host << "--host=" << config->getHost();
    plugin_opts.push_back(tg_host.str());
    ostringstream tg_port;
    tg_port << "--port=" << config->getPort();
    plugin_opts.push_back(tg_port.str());

    plugin_opts.push_back("--replace=yes");
    plugin_opts.push_back("--sockets=yes");
    if (config->getTracegrindAlarm() != 0)
    {
      alarm(config->getTracegrindAlarm());
    }
    killed = false;
  }
  else if (config->usingDatagrams())
  {
    plugin_opts.push_back("--replace=yes");
    plugin_opts.push_back("--datagrams=yes");
    if (config->getTracegrindAlarm() != 0)
    {
      alarm(config->getTracegrindAlarm());
    }
  killed = false;
  }      
  else
  {
    for (int i = 0; i < config->getNumberOfFiles(); i++)
    {
      plugin_opts.push_back(string("--file=") + config->getFile(i));
    }
  }
  if (config->getCheckArgv() != "")
  {
    plugin_opts.push_back("--check-argv=" + config->getCheckArgv());
  }
}

void ExecutionManager::getCovgrindOptions(vector <string> &plugin_opts, string fileNameModifier, bool addNoCoverage)
{
  string cur_temp_dir = temp_dir;
  if (config->getRemoteValgrind() != "")
  {
    cur_temp_dir = string("");
  }
  plugin_opts.push_back("-v");
  if (config->usingSockets())
  {
    ostringstream cv_host;
    cv_host << "--host=" << config->getHost();
    plugin_opts.push_back(cv_host.str());

    ostringstream cv_port;
    cv_port << "--port=" << config->getPort();
    plugin_opts.push_back(cv_port.str());
    
    plugin_opts.push_back(string("--replace=") + cur_temp_dir + string("replace_data") + fileNameModifier);
    plugin_opts.push_back("--sockets=yes");

    LOG(Logger::DEBUG, "Setting alarm " << config->getAlarm() << ".");
    alarm(config->getAlarm());
    killed = false;
  }
  else if (config->usingDatagrams())
  { 
    plugin_opts.push_back(string("--replace=") + cur_temp_dir + string("replace_data") + fileNameModifier);
    plugin_opts.push_back("--datagrams=yes");

    LOG(Logger::DEBUG, "Setting alarm " << config->getAlarm() << ".");
    alarm(config->getAlarm());
    killed = false;
  }
  else
  {
    ostringstream cv_alarm;
    cv_alarm << "--alarm=" << config->getAlarm();
    plugin_opts.push_back(cv_alarm.str());
  }

  if (config->getRemoteValgrind() == "")
  {
    string cv_exec_file = cur_temp_dir + string("execution") + fileNameModifier + string(".log");
    plugin_opts.push_back(string("--log-file=") + cv_exec_file);
  }

  if (config->checkForLeaks())
  {
    plugin_opts.push_back("--leak-check=full");
  }

  if (addNoCoverage)
  {
    plugin_opts.push_back("--no-coverage=yes");
  }
  plugin_opts.push_back(string("--filename=") + cur_temp_dir + string("basic_blocks") + fileNameModifier + string(".log"));
}

static
string replaceNumber(string src, const char *pattern)
{
    size_t position = 0, initial_position = 0;
    while (true)
    {
        position = src.find(pattern, initial_position);
        if (position == string::npos) return src;
        position += strlen(pattern);
        initial_position = position;
        while(position < src.length())
        {
            if (!isdigit(src[position]) && !isalpha(src[position]))
            {
                break;
            }
            position ++;
        }
        src.replace(initial_position, position - initial_position, "?");
    }
    return src;
}

static
string filterErrorInfo(string src)
{
    src = replaceNumber(src, "0x");
    src = replaceNumber(src, "of size ");
    src = replaceNumber(src, "loss record ");
    return src;
}

int ExecutionManager::dumpError(Input *input, Error *error)
{
    int i = 0, same_exploit = -1;
    int error_i = -1;
    ostringstream ss_input_file;
    ostringstream ss_command;
    string input_file_m, cur_error_trace;
    
    LOG(Logger::VERBOSE, "");
    LOG_TIME(Logger::VERBOSE, "Error detected.");
    
    error_i = error->getSubtypeNumber();

    input_file_m = config->getResultDir() + config->getPrefix() + 
                        error->getFileNameModifier() + "_";

        
    Error *active_err;

    if (error->getTrace() != "")
    {
        for (vector<Error*>::iterator it = report.begin(); 
                                      it != report.end(); 
                                      it ++, i ++)
        {
            cur_error_trace = filterErrorInfo((*it)->getTrace());
            if (cur_error_trace == filterErrorInfo(error->getTrace()))
            {
                same_exploit = i;
                (*it)->addInput(error_i);
                active_err = *it;
                break;
            }
        }
        if (same_exploit == -1) 
        {
            active_err = error;
            error->addInput(error_i);
            report.push_back(active_err);
            same_exploit = report.size();
        }
        if (active_err->getStatus() == OTHER_SIGNAL)
        {
            LOG(Logger::REPORT, "  \033[31mWarning: terminating signal wasn't sent by kernel"
                                " or the analyzed process.\n  Manual checking required to"
                                " validate the error.\033[0m");
        }
    }
    else
    {
        active_err = error;
        error->addInput(error_i);
        report.push_back(active_err);
        same_exploit = report.size();
        LOG(Logger::REPORT, "  \033[31mWarning: application was likely terminated"
                            " with SIGKILL signal.\n  Manual checking required"
                            " to validate the error.\033[0m");
    }

    string shifted_error_trace = "  ";
    string error_trace = active_err->getTraceBody();
    for (int i = 0; i < error_trace.size(); i ++)
    {
        shifted_error_trace.push_back(error_trace[i]);
        if (error_trace[i] == '\n')
        {
            shifted_error_trace.append("  ");
        }
    }
    if (config->getVerbose())
    {
        LOG(Logger::JOURNAL, "  \033[31m" << active_err->getTraceHeader() << "\033[0m");
    }
    else
    {
        LOG(Logger::JOURNAL, "  \033[31m" << active_err->getShortName() << "\033[0m");
    }
    if (same_exploit != report.size())
    {
        LOG(Logger::VERBOSE, "  \033[2mError was detected previously.\033[0m");
    }
    else
    {
        LOG(Logger::VERBOSE, shifted_error_trace);
    }

    if (config->usingSockets() || config->usingDatagrams())
    {
        ss_input_file << input_file_m << error_i;
        LOG(Logger::VERBOSE, "  Dumping input to file " << ss_input_file.str());
        if (input->dumpExploit(ss_input_file.str(), false) < 0)
        {
            if (same_exploit == report.size())
            {
                report.erase(report.end() - 1);
            }
            return -1;
        }

        ss_command << " " << config->getValgrind() + config->getValgrindPath() <<  " --tool=covgrind --host=" <<
                      config->getHost() << " --port=" << config->getPort() << 
                      " --replace=" << ss_input_file.str () << " --sockets=yes";
    }
    else
    {
        int f_num = input->files.size();
        if ((config->getCheckArgv() != ""))
        {
            f_num --;
        }
        for (int i = 0; i < f_num; i++)
        {
            ostringstream ss_m_input_file;
            ss_m_input_file << input_file_m << error_i << "_" << i;
            LOG(Logger::VERBOSE, "  Dumping input to file " << 
                                 ss_m_input_file.str() << ".");
            if (input->files.at(i)->dumpFile(ss_m_input_file.str()) < 0)
            {
                if (same_exploit == report.size())
                {
                    report.erase(report.end() - 1);
                }
                return -1;
            }
        }
    }
    if ((active_err->getType() != CRASH) && (active_err->getType() != UNKNOWN))
    {
        ss_command << config->getValgrind() + config->getValgrindPath() << " --tool=" << config->getPlugin() << " ";
    }
    for (vector<string>::iterator it = cur_argv.begin (); 
                                  it != cur_argv.end (); 
                                  it ++)
    {   
        bool replaced_file = false;
        for (int j = 0; j < config->getNumberOfFiles(); j ++)
        { 
            if (config->getFile(j) == *it)
            {       
                ss_command << " " << input_file_m << error_i << "_" << j;
                replaced_file = true;
                break;
            }
        }
        if (!replaced_file)
        {
            ss_command << " " << *it;
        }
    }
    LOG(Logger::JOURNAL, "  \033[2mCommand:\033[0m " << ss_command.str());

    if (same_exploit == report.size())
    {
        active_err->setCommand(ss_command.str());
    }
    active_err->updateCommand(ss_command.str());

    LOG(Logger::JOURNAL, ""); // new line after exploit report
    return same_exploit;
}

int ExecutionManager::calculateScore(string fileNameModifier)
{
  bool enable_mutexes = (fileNameModifier != string(""));
  int res = 0;
  int fd = open((temp_dir + string("basic_blocks") + fileNameModifier + string(".log")).c_str(), 
                O_RDONLY, S_IRUSR | S_IROTH | S_IRGRP | S_IWUSR | S_IWOTH | S_IWGRP);
  if (fd != -1)
  {
    struct stat fileInfo;
    fstat(fd, &fileInfo);
    int size = fileInfo.st_size / config->getSizeOfLong();
    if (size > 0)
    {
      if (config->getSizeOfLong() == 4)
      {
        unsigned int basicBlockAddrs[size];
        read(fd, basicBlockAddrs, fileInfo.st_size);
        close(fd);
        if (enable_mutexes) pthread_mutex_lock(&add_bb_mutex);
        for (int i = 0; i < size; i++)
        {
          if (basicBlocksCovered.find(basicBlockAddrs[i]) == basicBlocksCovered.end())
          {
            res++;
          }
          if(thread_num < 1)
          {
            basicBlocksCovered.insert(basicBlockAddrs[i]);
          }
          else
          {
            delta_basicBlocksCovered.insert(basicBlockAddrs[i]);
          }
        }
      }
      else if (config->getSizeOfLong() == 8)
      {
        unsigned long long basicBlockAddrs[size];
        read(fd, basicBlockAddrs, fileInfo.st_size);
        close(fd);
        if (enable_mutexes) pthread_mutex_lock(&add_bb_mutex);
        for (int i = 0; i < size; i++)
        {
          if (basicBlocksCovered.find(basicBlockAddrs[i]) == basicBlocksCovered.end())
          {
            res++;
          }
          if(thread_num < 1)
          {
            basicBlocksCovered.insert(basicBlockAddrs[i]);
          }
          else
          {
            delta_basicBlocksCovered.insert(basicBlockAddrs[i]);
          }
        }
      }
      if (enable_mutexes) pthread_mutex_unlock(&add_bb_mutex);
    }
  }
  else
  {
    LOG(Logger::ERROR, "Cannot open file " << temp_dir << "basic_blocks" <<
                       fileNameModifier << ".log: " << strerror(errno));
    return -1;
  }
  return res;
}

// Run Valgrind or Memcheck on 'input'

int ExecutionManager::checkAndScore(Input* input, bool addNoCoverage, bool first_run, string fileNameModifier)
{
  if (config->usingSockets() || config->usingDatagrams())
  {
    string replace_data = temp_dir + string("replace_data");
    if (input->dumpExploit(replace_data, false, fileNameModifier.c_str()) < 0)
    {
      return -1;
    }
  }
  else
  {
    if (input->dumpFiles(fileNameModifier.c_str()) < 0)
    {
      return -1;
    }
  }
  vector<string> plugin_opts;
  getCovgrindOptions(plugin_opts, fileNameModifier, addNoCoverage);

  string cv_exec_file = temp_dir + string("execution") + fileNameModifier + string(".log");
  
  if (!first_run && (config->getCheckArgv() != ""))
  {
    if (!updateArgv(input))
    {
      return -1;
    }
  }
  vector <string> new_prog_and_args = cur_argv;
  vector<char> to_send(new_prog_and_args.size() + plugin_opts.size(), '\0');
  if (!(config->usingSockets()) && !(config->usingDatagrams()))
  {
    for (int i = 0; i < new_prog_and_args.size(); i ++)
    {
      for (int j = 0; j < input->files.size(); j ++)
      {
        if (!strcmp(new_prog_and_args[i].c_str(), input->files.at(j)->getName().c_str()))
        {
          if (fileNameModifier != string(""))
          {
            new_prog_and_args[i].append(fileNameModifier);
          }
          to_send[plugin_opts.size() + i] = 1;
        }
      }
    }
  }

  string plugin_name;
  if (addNoCoverage)
  {
    plugin_name = "--tool=covgrind";
  }
  else
  {
    plugin_name = string("--tool=") + config->getPlugin();
  }
  plugin_opts.insert(plugin_opts.begin(), plugin_name);

  Executor* plugin_exe;
  if (config->getRemoteValgrind() == "")
  {

    plugin_exe = new PluginExecutor(config->getDebug(), config->getTraceChildren(),
                                     config->getValgrind() + config->getValgrindPath(), new_prog_and_args, 
                                     plugin_opts);
  }
  else
  {
    vector <string> plug_args = plugin_opts;
    for (int i = 0; i < new_prog_and_args.size(); i ++)
    {
      plug_args.push_back(new_prog_and_args[i]);
    }
    to_send.insert(to_send.begin(), 0);
    plugin_exe = new RemotePluginExecutor(plug_args, remote_fd, to_send, 
                                          config->getResultDir());
  }
  new_prog_and_args.clear();
  plugin_opts.clear();
  bool enable_mutexes = (config->getSTPThreads() != 0) && !first_run;
  int thread_index = (fileNameModifier == string("")) ? 0 : atoi(fileNameModifier.substr(1).c_str());
  monitor->setState(CHECKER, time(NULL), thread_index);

  // Covgrind or Memcheck run

  int exitCode;
  exitCode = plugin_exe->run(thread_index);
  delete plugin_exe;
  if (exitCode == 1)
  {
    return -1;
  }

  monitor->addTime(time(NULL), thread_index);
  FileBuffer* mc_output;
  bool has_crashed = (exitCode == -1);

  ExecutionLogBuffer *plugin_log;
  try
  {
    plugin_log = new ExecutionLogBuffer(cv_exec_file);
  }
  catch(const char *)
  {
    return -1;
  }
  catch(std::bad_alloc)
  {
    LOG(Logger::ERROR, strerror(errno));
    return -1;
  }

  if (enable_mutexes)
  {
    pthread_mutex_lock(&add_exploits_mutex);
  }
  int res;
  vector<Error*> error_list = plugin_log->getErrors(config->getPlugin());
  for (vector<Error*>::iterator it = error_list.begin(); 
                                it != error_list.end(); 
                                it ++)
  {
    if ((res = dumpError(input, *it)) < 0)
    {
      if (enable_mutexes)
      {
        pthread_mutex_unlock(&add_exploits_mutex);
      }
      return -1;
    }
    if (it == error_list.end() - 1)
    {
      (*it)->incSubtypeNumber();
    }
    if (res != report.size())
    {
      delete *it;
    }
  }
  if (has_crashed)
  {
    Error* new_error = plugin_log->getCrashError();
    if (dumpError(input, new_error) < 0)
    {
      if (enable_mutexes)
      {
          pthread_mutex_unlock(&add_exploits_mutex);
      }
      return -1;
    }
    new_error->incSubtypeNumber();
  }
  
  if (enable_mutexes) 
  {
    pthread_mutex_unlock(&add_exploits_mutex);
  }
  int result = 0;
  if (!addNoCoverage)
  {
    result = calculateScore(fileNameModifier);
  }
  delete plugin_log;
  return result;
}

int ExecutionManager::checkDivergence(Input* first_input, int score)
{
  string div_file = temp_dir + string("divergence.log");
  int divfd = open(div_file.c_str(), O_RDONLY);
  if (divfd != -1)
  {
    bool divergence;
    read(divfd, &divergence, sizeof(bool));
    if (divergence)
    {
      int d;
      read(divfd, &d, sizeof(int));
      LOG(Logger::DEBUG, "Divergence at depth " << d << ".");
      if (config->usingSockets() || config->usingDatagrams())
      {
        ostringstream ss;
        ss << config->getPrefix() << "divergence_" << divergences;
        if (first_input->dumpExploit((char*) ss.str().c_str(), false) < 0)
        {
          return -1;
        }
        LOG(Logger::DEBUG, "Dumping divergent input to file " << ss.str());
        
      }
      else
      {
        for (int i = 0; i < first_input->files.size(); i++)
        {
          ostringstream ss;
          ss << config->getPrefix() << "divergence_" << divergences << "_" << i;
          if (first_input->files.at(i)->FileBuffer::dumpFile(ss.str()) < 0)
          {
            return -1;
          }
          LOG(Logger::DEBUG, "Dumping divergent input to file " << ss.str());
        }
      }
      divergences++;
      LOG(Logger::DEBUG, "with startdepth = " << first_input->startdepth << " and invertdepth = " << config->getDepth() << "\n");
      close(divfd);
      if (score == 0) 
      {
        if (is_distributed)
        {
          talkToServer();
        }
        return 1;
      }
    }
  }
  return 0;
}

// Read new input from sockets

void ExecutionManager::updateInput(Input* input)
{
  string replace_data = temp_dir + string("replace_data");
  int fd = open(replace_data.c_str(), O_RDONLY);
  int socketsNum;
  read(fd, &socketsNum, sizeof(int));
  for (int i = 0; i < socketsNum; i++)
  {
    int chunkSize;
    read(fd, &chunkSize, sizeof(int));
    if (i >= input->files.size())
    {
      input->files.push_back(new SocketBuffer(i, chunkSize));
    }
    else if (input->files.at(i)->getSize() < chunkSize)
    {
      input->files.at(i)->setSize(chunkSize);
      input->files.at(i)->buf = (char*) realloc(input->files.at(i)->buf, chunkSize);
      memset(input->files.at(i)->buf, 0, chunkSize);
    }
    read(fd, input->files.at(i)->buf, chunkSize);
  }
  close(fd);
}

void alarmHandler(int signo)
{
  LOG(Logger::JOURNAL, "Time is out.");
  if (!nokill)
  {
    monitor->handleSIGALARM();
    killed = true;
    LOG(Logger::DEBUG, "Time out. Valgrind is going to be killed.");
  }
  signal(SIGALRM, alarmHandler);
}

void* process_query(void* data)
{
  PoolThread* actor = (PoolThread*) data;
  ExecutionManager* this_pointer = 
             (ExecutionManager*) (Thread::getSharedData("this_pointer"));
  multimap<Key, Input*, cmp>* inputs = 
             (multimap <Key, Input*, cmp> *) (Thread::getSharedData("inputs"));
  Input* first_input = (Input*) (Thread::getSharedData("first_input"));
  bool* actual = (bool*) (Thread::getSharedData("actual"));
  long first_depth = (long) (Thread::getSharedData("first_depth"));
  long depth = (long) (actor->getPrivateData("depth"));
  int cur_tid = actor->getCustomTID();
  if (this_pointer->processQuery(first_input, actual,
                                 first_depth, depth, cur_tid) < 0)
  {
    f_error = true;
  }
  return NULL;
}

int ExecutionManager::parseOffsetLog(vector<FileOffsetSet> &used_offsets)
{
  FileOffsetSet cur_offset_set;
  string cur_file_name;
  bool read_file_name = true;
  bool saved_name = false;
  char value;
  unsigned long count = 0;
  int fd = open((temp_dir + "offsets.log").c_str(), O_RDONLY,
                 S_IRUSR | S_IROTH | S_IRGRP | S_IWUSR | S_IWOTH | S_IWGRP);
  if (fd < 0)
  {
    LOG(Logger::ERROR, 
            "Cannot open file " << temp_dir << 
            "offsets.log: " << strerror(errno));                    
    return 0;
  }
  while (read(fd, &value, 1) > 0)
  {
    if (value == '\1')
    {
      cur_offset_set.offset_set.insert(count);
      read_file_name = false;
      count ++;
    }
    else if (value == '\n')
    {
      used_offsets.push_back(cur_offset_set);
      cur_offset_set.offset_set.clear();
      cur_file_name.clear();
      count = 0;
      saved_name = false;
    }
    else if (value == '\0')
    {
      read_file_name = false;
      count ++;
    }
    if (read_file_name)
    {
      cur_file_name.push_back(value);
    }
    else if (!saved_name)
    {
      cur_offset_set.file_name = cur_file_name;
      saved_name = true;
    }
  }
  close(fd);
  return 1;
}

// Run STP

int ExecutionManager::processQuery(Input* first_input, bool* actual, unsigned long first_depth, unsigned long cur_depth, unsigned int thread_index)
{
    string cur_trace_log = temp_dir;
    cur_trace_log += (trace_kind) ? string("curtrace") : string("curdtrace");
    string input_modifier = string("");
    if (thread_index)
    {
        ostringstream input_modifier_s;
        input_modifier_s << "_" << thread_index;
        input_modifier = input_modifier_s.str();
    }
    cur_trace_log += input_modifier + string(".log");
    STP_Executor stp_exe(getConfig()->getDebug(), getConfig()->getValgrind());        
    monitor->setState(STP, time(NULL), thread_index);
    string stp_out = stp_exe.run(cur_trace_log.c_str(), thread_index);
    monitor->addTime(time(NULL), thread_index);
    if (stp_out == string(""))
    {
        if (!monitor->getKilledStatus())
        {
            LOG(Logger::ERROR, "STP has encountered an error.");
            try
            {
                FileBuffer f(cur_trace_log);
                LOG(Logger::ERROR, cur_trace_log.c_str() << ":\n" << f.buf);
            }
            catch (const char *msg)
            {
                return -1;
            }
        }
    }
    else
    {
        FileBuffer *stp_out_file = NULL;
        try
        {
            stp_out_file = new FileBuffer(stp_out);
        }
        catch (const char *msg)
        {
            return -1;
        }
        vector<FileOffsetSet> used_offsets;
        parseOffsetLog(used_offsets);
        LOG(Logger::DEBUG, "\033[2m" << stp_out_file->buf << "\033[0m");
        Input* next = new Input();
        int st_depth = first_input->startdepth;
        for (int k = 0; k < first_input->files.size(); k++)
        { 
            FileBuffer* fb = first_input->files.at(k);
            fb = fb->forkInput(stp_out_file, used_offsets);
            if (fb == NULL)
            {
                delete next;
                next = NULL;
                break;
            }
            else
            {
                next->files.push_back(fb);
            }
        }
        delete stp_out_file;
        if (next != NULL)
        {
            next->startdepth = st_depth + cur_depth + 1;
            next->prediction = new bool[st_depth + cur_depth];
            for (int j = 0; j < st_depth + cur_depth - 1; j++)
            {
                next->prediction[j] = actual[j];
            }
            next->prediction[st_depth + cur_depth - 1] = 
                                  !actual[st_depth + cur_depth - 1];
            next->prediction_size = st_depth + cur_depth;
            next->parent = first_input;
            if ((thread_index > 0) && (config->getRemoteValgrind() != ""))
            {
                pthread_mutex_lock(&add_remote_mutex);
                remote_inputs.push(make_pair(next, first_depth + cur_depth + 1));
                pthread_mutex_unlock(&add_remote_mutex);
                pthread_cond_signal(&input_available_cond);
            }
            else
            {
                int score = checkAndScore(next, !trace_kind, false,  
                                          input_modifier);
                if (score == -1)
                {
                    return -1;
                }
                if (trace_kind)
                {
                    if (thread_index)
                    {
                        LOG(Logger::DEBUG, "Thread #" << thread_index << 
                                           ": Score = " << score << ".");
                        pthread_mutex_lock(&add_inputs_mutex);
                    }
                    else
                    {
                        LOG(Logger::DEBUG, "Score = " << score << ".");
                    }
                    inputs.insert(make_pair(Key(score, first_depth + cur_depth + 1), next));
                    if (thread_index) 
                    {
                        pthread_mutex_unlock(&add_inputs_mutex);
                    }
                }
            }
        }
    }
    return 0;
}

void ExecutionManager::addInput(Input* input, unsigned int depth, 
                                unsigned int score)
{
    inputs.insert(make_pair(Key(score, depth), input));
}

void* launch_cv(void* data)
{
    while(true)
    {
        pthread_mutex_lock(&add_remote_mutex);
        if ((remote_inputs.size() == 0) && !launch_cv_stop)
        {
            pthread_cond_wait(&input_available_cond, &add_remote_mutex);
        }
        if (launch_cv_stop && (remote_inputs.size() == 0))
        {
            pthread_mutex_unlock(&add_remote_mutex);
            break;
        }
        if (remote_inputs.size() > 0)
        {
            pair<Input*, unsigned int> remote_input = remote_inputs.top();
            remote_inputs.pop();
            ExecutionManager* this_pointer = (ExecutionManager*) data;
            int score = 
                  this_pointer->checkAndScore(remote_input.first, !trace_kind,
                                              false, "");
            if (score == -1)
            {
                return (void*) (-1);
            }
            LOG(Logger::REPORT, "Score = " << score << ".");
            pthread_mutex_lock(&add_inputs_mutex);
            this_pointer->addInput(remote_input.first, 
                                   remote_input.second, score);
            pthread_mutex_unlock(&add_inputs_mutex);
        }
        pthread_mutex_unlock(&add_remote_mutex);
    }
    return NULL;
}

int ExecutionManager::processTraceParallel(Input * first_input, 
                                           unsigned long first_depth)
{
    string actual_file_name = temp_dir + string("actual.log");
    int actual_fd = open(actual_file_name.c_str(), O_RDONLY, S_IRUSR);
    if (actual_fd == -1)
    {
        LOG(Logger::ERROR, "Cannot open file " << actual_file_name <<
                           " :" << strerror(errno));
        return -1;
    }
    int actual_length;
    if (config->getDepth() == 0)
    {
        if (read(actual_fd, &actual_length, sizeof(int)) < 1)
        {
             LOG(Logger::ERROR, "Cannot read from file " << actual_file_name <<
                                " :" << strerror(errno));
             close(actual_fd);
             return -1;
        }
    }
    else
    {
        actual_length = first_input->startdepth - 1 + config->getDepth();
    }
    bool actual[actual_length];
    if (read(actual_fd, actual, actual_length * sizeof(bool)) < 1)
    {
        LOG(Logger::ERROR, "Cannot read from file " << actual_file_name <<
                                " :" << strerror(errno));
        close(actual_fd);
        return -1;
    }
    close(actual_fd);
    int active_threads = thread_num;
    long depth = 0;
    string trace_file = temp_dir + ((trace_kind) ? string("trace.log") 
                                                 : string("dangertrace.log"));
    FileBuffer *trace;
    try
    {
        trace = new FileBuffer(trace_file);
    }
    catch (const char *msg)
    {
        return -1;
    }
    catch (std::bad_alloc)
    {
        LOG(Logger::ERROR, strerror(errno));
        return -1;
    }
    Thread::clearSharedData();
    Thread::addSharedData((void*) &inputs, string("inputs"));
    Thread::addSharedData((void*) first_input, string("first_input"));
    Thread::addSharedData((void*) first_depth, string("first_depth"));
    Thread::addSharedData((void*) actual, string("actual"));
    Thread::addSharedData((void*) this, string("this_pointer"));
    char* query = trace->buf;
    while((query = strstr(query, "QUERY(FALSE);")) != NULL)
    {
        depth ++;
        query ++;
    }
    for (int j = 0; j < ((depth < thread_num) ? depth : thread_num); j ++)
    {
        threads[j].setCustomTID(j + 1);
        threads[j].setPoolSync(&finish_mutex, &finish_cond, &active_threads);
    }
    int thread_counter;
    job_wrapper external_data[depth];
    if (config->getRemoteValgrind() != "")
    {
        job_wrapper remote_external_data;
        remote_external_data.work_func = launch_cv;
        remote_external_data.data = this;
        launch_cv_stop = false;
        remote_thread.createThread(&remote_external_data);
    }
    for (int i = 0; i < depth; i ++)
    {
        pthread_mutex_lock(&finish_mutex);
        if (active_threads == 0) 
        {
            pthread_cond_wait(&finish_cond, &finish_mutex);
        }
        for (thread_counter = 0; thread_counter < thread_num; thread_counter ++) 
        {
            if (threads[thread_counter].getStatus())
            {
                break;
            }
        }
        if (threads[thread_counter].getStatus() == PoolThread::FREE)
        {
            threads[thread_counter].waitForThread();
        }
        active_threads --;
        threads[thread_counter].addPrivateData((void*) i, string("depth"));
        external_data[i].work_func = process_query;
        external_data[i].data = &(threads[thread_counter]);
        ostringstream cur_trace;
        if (trace_kind)
        {
            cur_trace << temp_dir << "curtrace_";
        }
        else
        {
            cur_trace << temp_dir << "curdtrace_";
        } 
        cur_trace << thread_counter + 1 << ".log";
        if (trace->cutQueryAndDump(cur_trace.str().c_str(), trace_kind) < 0)
        {
            pthread_mutex_unlock(&finish_mutex);
            f_error = true;
            break;
        }
        in_thread_creation = thread_counter;
        threads[thread_counter].setStatus(PoolThread::BUSY);
        threads[thread_counter].createThread(&(external_data[i]));
        in_thread_creation = -1;
        pthread_mutex_unlock(&finish_mutex);
    }
    for (int i = 0; i < ((depth < thread_num) ? depth : thread_num); i ++)
    {
        threads[i].waitForThread();
    }
    if (config->getRemoteValgrind() != "")
    {
        pthread_mutex_lock(&add_remote_mutex);
        launch_cv_stop = true;
        pthread_mutex_unlock(&add_remote_mutex);
        pthread_cond_signal(&input_available_cond);
        remote_thread.waitForThread();
    }
    delete trace;
    if (f_error)
    {
        return -1;
    }
    return depth;
}

/* Trace processing for single-thread mode. */

int ExecutionManager::processTraceSequental(Input* first_input, 
                                            unsigned long first_depth)
{
    string actual_file_name = temp_dir + string("actual.log");
    int actual_fd = open(actual_file_name.c_str(), O_RDONLY, S_IRUSR);
    char *query;
    int actual_length, depth = 0;
    if (actual_fd == -1)
    {
        LOG(Logger::ERROR, "Cannot open file " << actual_file_name <<
                           " :" << strerror(errno));
        return -1;
    }
    if (config->getDepth() == 0)
    {
        if (read(actual_fd, &actual_length, sizeof(int)) < 1)
        {
            LOG(Logger::ERROR, "Cannot read from file " << actual_file_name <<
                               " :" << strerror(errno));
            close(actual_fd);
            return -1;
        }
    }
    else
    {
        actual_length = first_input->startdepth - 1 + config->getDepth();
    }
    bool actual[actual_length];
    if (read(actual_fd, actual, actual_length * sizeof(bool)) < 1)
    {
        LOG(Logger::ERROR, "Cannot read from file " << actual_file_name <<
                               " :" << strerror(errno));
        close(actual_fd);
        return -1;
    }
    close(actual_fd);
    try
    {
        if (config->getCheckDanger())
        {
            int cur_depth = 0;
            trace_kind= false;

            FileBuffer dtrace(temp_dir + string("dangertrace.log"));
            while ((query = strstr(dtrace.buf, "QUERY(FALSE)")) != NULL)
            {
                dtrace.cutQueryAndDump(temp_dir + string("curdtrace.log"));
                if (processQuery(first_input, actual, 
                                 first_depth, cur_depth ++) < 0)
                {
                    return -1;
                }
            }
        }
        trace_kind = true;
        FileBuffer trace(temp_dir + string("trace.log"));
        while((query = strstr(trace.buf, "QUERY(FALSE)")) != NULL)
        {
            depth++;
            trace.cutQueryAndDump(temp_dir + string("curtrace.log"),
                                  true);
            if (processQuery(first_input, actual, 
                             first_depth, depth - 1) < 0)
            {
                return -1;
            }
        }
    }
    catch (const char *msg)
    {
        depth = -1;
    }
    return depth;
}

void dummy_handler(int signo)
{

}

int ExecutionManager::requestNonZeroInput()
{
  multimap<Key, Input*, cmp>::iterator it = --(inputs.end());
  int best_score = it->first.score;
  if ((best_score == 0) && config->getAgent())
  {
    LOG(Logger::VERBOSE, "All inputs have zero score: requesting new input.");
    signal(SIGUSR2, dummy_handler);
    kill(getppid(), SIGUSR1);
    pause();
    string startdepth_file = temp_dir + string("startdepth.log");
    int descr = open(startdepth_file.c_str(), O_RDONLY | O_CREAT, 
                     S_IRUSR | S_IROTH | S_IRGRP | S_IWUSR | S_IWOTH | S_IWGRP);
    int startdepth = 0;
    read(descr, &startdepth, sizeof(int));
    close(descr);
    if (startdepth > 0)
    {
      return startdepth;
    }
    config->setNotAgent();
    inputs.erase(it);
  }
  else
  {
    inputs.erase(it);
  }
  return 0;
}

bool ExecutionManager::updateArgv(Input* input)
{
  int cur_opt = 1, cur_offset = 0;
//  int ctrl_counter = 0;
//  bool reached_zero = false;
//  bool reached_normal = false;
  char* argv_val = input->files.at(input->files.size() - 1)->buf;
  string spaced_mask = string(" ") + config->getCheckArgv() + " ";
  char buf[16];
/*  if ((!valid_char(argv_val[0]) || (argv_val[0] == ' ')) && (argv_val[0] != 0))
  {
    REPORT(logger, "Discarding input - argument starting with control character\n");
    return false;
  }
  else
  {
    reached_normal = true;
  }*/
  for (int i = 0; i < args_length; i ++)
  {
    sprintf(buf, " %d ", cur_opt);
    if (spaced_mask.find(buf) != string::npos)
    {
      cur_argv[cur_opt][cur_offset] = argv_val[i];
    }
    cur_offset ++;
    /*if (!valid_char(argv_val[i]))
    {
      if (ctrl_counter && reached_normal && !reached_zero && (argv_val[i]))
      {
        REPORT(logger, "Discarding input - multiple control characters\n");
        return false;
      }
      if (argv_val[i] == 0)
      {
        reached_zero = true;
      }
      else
      {
        ctrl_counter = 1;
      }
    }
    else
    {
      reached_normal = true;
    }*/
    if (cur_offset == cur_argv[cur_opt].size())
    {
      //ctrl_counter = 0;
      i ++;
      cur_opt ++;
      cur_offset = 0;
      /*if (i + 1 < args_length)
      {
        if ((!valid_char(argv_val[i + 1]) || (argv_val[i + 1] == ' ')) && (argv_val[i + 1] != 0))	
        {
          REPORT(logger, "Discarding input - argument starting with control character\n");
          return false;
        }
      }*/
    }
  }
  return true;
}  

void ExecutionManager::run()
{
//    LOG(Logger::DEBUG, "Running execution manager.");
    if (config->getCheckArgv() != "")
    {
      string arg_lengths = temp_dir + string("arg_lengths");
      int fd = open(arg_lengths.c_str(), O_CREAT | O_TRUNC | O_WRONLY, 
                    S_IRUSR | S_IROTH | S_IRGRP | S_IWUSR | S_IWOTH | S_IWGRP);
      int length;
      for (int i = 1; i < cur_argv.size(); i ++)
      {
        length = cur_argv[i].size();
        write(fd, &length, sizeof(int));
      }
      close(fd);
    }
    int runs = 0;

    // Reading files into initial input

    initial = new Input();
    if (!config->usingSockets() && !config->usingDatagrams())
    {
      for (int i = 0; i < config->getNumberOfFiles(); i++)
      {
        try
        {
          initial->files.push_back(new FileBuffer(config->getFile(i)));
        }
        catch (const char *)
        {
          return;
        }
        catch (std::bad_alloc)
        {
          LOG(Logger::ERROR, strerror(errno));
          return;
        }
      }
    }
    else 
    {
      if (config->getAgent())
      {
        updateInput(initial);
      }
      signal(SIGALRM, alarmHandler);
    }
    initial->startdepth = config->getStartdepth();
    int score = checkAndScore(initial, false, true, "");
    if (score < 0)
    {
      return;
    }
    basicBlocksCovered.insert(delta_basicBlocksCovered.begin(), delta_basicBlocksCovered.end());
    LOG(Logger::DEBUG, "First score = " << score << ".");
    inputs.insert(make_pair(Key(score, 0), initial));
    bool delete_fi;
    
    while (!inputs.empty()) 
    {
      delete_fi = false;
      LOG_TIME(Logger::JOURNAL, "Iteration " << (runs + 1) << ".");

      monitor->removeTmpFiles();
      delta_basicBlocksCovered.clear();
      multimap<Key, Input*, cmp>::iterator it = --(inputs.end());
      Input* fi = it->second; // first input
      unsigned int scr = it->first.score;
      unsigned int dpth = it->first.depth;
      LOG(Logger::VERBOSE, "Inputs size = " << inputs.size() << ".");
      LOG(Logger::VERBOSE, "Selected next input with score " << scr << ".");

      if (config->usingSockets() || config->usingDatagrams())
      {
        fi->dumpExploit((temp_dir + string("replace_data")).c_str(), true);
      }
      else
      {
        fi->dumpFiles();
      }

      // Options for Tracegrind

      ostringstream tg_depth;
      vector<string> plugin_opts;
      bool newInput = false;

      int startdepth = requestNonZeroInput();
      if (startdepth)
      {
        tg_depth << "--startdepth=" << startdepth;
        newInput = true;
      }
      else
      {
        tg_depth << "--startdepth=" << fi->startdepth;
        plugin_opts.push_back(tg_depth.str());
        if (runs > 0)
        {
          plugin_opts.push_back("--check-prediction=yes");
        }
      }
  
      getTracegrindOptions(plugin_opts);

      if (config->getRemoteValgrind() == "")
      {
        plugin_opts.push_back(string("--log-file=") + 
                              temp_dir + string("execution.log"));
      }

      if (runs && (config->getCheckArgv() != ""))
      {
        updateArgv(fi);
      }

      vector <string> plug_args = plugin_opts;
      for (int i = 0; i < cur_argv.size(); i ++)
      {
        plug_args.push_back(cur_argv[i]);
      }
      vector <char> to_send(plug_args.size(), '\0');
      if (!(config->usingSockets()) && !(config->usingDatagrams()))
      {
        for (int i = 0; i < cur_argv.size(); i ++)
        {
          for (int j = 0; j < fi->files.size(); j ++)
          {
            if (cur_argv[i] == fi->files.at(j)->getName())
            {
              to_send[plugin_opts.size() + i] = 1;
            }
          }
        }
      }
      if (runs == 0)
      {
        for (int i = 0; i < plug_args.size(); i ++)
        {
          if ((plug_args[i].find("--mask") != string::npos) ||
              (plug_args[i].find("--func-filter") != string::npos))
          {
            to_send[i] = 1;
          }
        }
      }
      Executor * plugin_exe;
      if (config->getRemoteValgrind() != "")
      {
        plug_args.insert(plug_args.begin(), "--tool=tracegrind");
        to_send.insert(to_send.begin(), 0);
        plugin_exe = new RemotePluginExecutor(plug_args, remote_fd, to_send, 
                                              config->getResultDir());
      }
      else
      {
        plugin_opts.insert(plugin_opts.begin(), "--tool=tracegrind");
        plugin_exe = new PluginExecutor(config->getDebug(), 
                                         config->getTraceChildren(), 
                                         config->getValgrind() + config->getValgrindPath(), cur_argv, 
                                         plugin_opts);
      }
            
      plugin_opts.clear();
      if (config->getTracegrindAlarm() == 0)
      {
        nokill = true;
      }
      time_t start_time = time(NULL);
      monitor->setState(TRACER, start_time);

      // Tracegrind running

      int exitCode;
      exitCode = plugin_exe->run(); 
      if (exitCode == 1)
      {
        break;
      }

      if (config->getCheckArgv() != "")
      {
        if (!runs)
        {
          string argv_log = temp_dir + string("argv.log");
          config->addFile(argv_log);
          try
          {
            fi->files.push_back(new FileBuffer(argv_log));
          }
          catch (const char *)
          {
            return;
          }
          catch (std::bad_alloc)
          {
            LOG(Logger::ERROR, strerror(errno));
            return;
          }
        }
      }
      monitor->addTime(time(NULL));

      delete plugin_exe;
      if (config->getTracegrindAlarm() == 0)
      {      
        nokill = false;
      }
      if (config->usingSockets() || config->usingDatagrams())
      {
        updateInput(fi);
      }

      if (exitCode == -1)
      {
        LOG(Logger::DEBUG, "Failure in Tracegrind.");
      }

      if (config->getDebug() && (runs > 0) && !newInput)
      {
        if (checkDivergence(fi, scr))
        {
          runs ++;
          continue;
        }
      }
 
      if (config->getDumpCalls())
      {
        break;
      }
      int depth = 0;
      if (thread_num)
      {
        if (config->getCheckDanger())
        {
          trace_kind = false;
          depth = processTraceParallel(fi, dpth);
        }
        trace_kind = true;
        depth = processTraceParallel(fi, dpth);
      }
      else
      {
        depth = processTraceSequental(fi, dpth);
      }
        
      if (depth == 0)
      {
        LOG(Logger::DEBUG, "No QUERY's found.");
      }
      if (depth == -1)
      {
        break;
      }
      runs++;
      if (initial != fi)
      {
        delete fi;
      }
      basicBlocksCovered.insert(delta_basicBlocksCovered.begin(), delta_basicBlocksCovered.end());
      if (is_distributed)
      {
        talkToServer();
      }
    }
    if (!(config->usingSockets()) && !(config->usingDatagrams()))
    {
      initial->dumpFiles();
    }
}

static void writeToSocket(int fd, const void* b, size_t count)
{
  char* buf = (char*) b;
  size_t sent = 0;
  while (sent < count)
  {
    size_t s = write(fd, buf + sent, count - sent);
    if (s == -1)
    {
      throw "error writing to socket";
    }
    sent += s;
  }
}

static void readFromSocket(int fd, const void* b, size_t count)
{
  char* buf = (char*) b;
  size_t received = 0;
  while (received < count)
  {
    size_t r = read(fd, buf + received, count - received);
    if (r == 0)
    {
      throw "connection is down";
    }
    if (r == -1)
    {
      throw "error reading from socket";
    }
    received += r;
  }
}

void ExecutionManager::talkToServer()
{
  try
  {
    int size;
    int response_num;
    LOG(Logger::NETWORK_LOG, "Communicating with server.");
    fd_set readfds;
    FD_ZERO(&readfds);
    FD_SET(dist_fd, &readfds);
    struct timeval timer;
    timer.tv_sec = 0;
    timer.tv_usec = 0;
    select(dist_fd + 1, &readfds, NULL, NULL, &timer);
    int limit = config->getProtectMainAgent() ? N * agents : 1;
    while (FD_ISSET(dist_fd, &readfds)) 
    {
      char c = '\0';
      readFromSocket(dist_fd, &c, 1);
      if (c == 'a')
      {
        LOG(Logger::NETWORK_LOG, "Sending options and data.");
        writeToSocket(dist_fd, "r", 1); 
        //sending "r"(responding) before data - this is to have something different from "q", so that server
        //can understand that main avalanche finished normally
        readFromSocket(dist_fd, &response_num, sizeof(int));
        while (response_num > 0)
        {
          if (inputs.size() <= limit)
          {
            break;
          }
          multimap<Key, Input*, cmp>::iterator it = --inputs.end();
          it--;
          Input* fi = it->second;
          int filenum = fi->files.size();
          writeToSocket(dist_fd, &filenum, sizeof(int));
          bool sockets = config->usingSockets();
          writeToSocket(dist_fd, &sockets, sizeof(bool));
          bool datagrams = config->usingDatagrams();
          writeToSocket(dist_fd, &datagrams, sizeof(bool));
          for (int j = 0; j < fi->files.size(); j ++)
          {
            FileBuffer* fb = fi->files.at(j);
            if (!config->usingDatagrams() && ! config->usingSockets())
            {
              int namelength = config->getFile(j).length();
              writeToSocket(dist_fd, &namelength, sizeof(int));
              writeToSocket(dist_fd, config->getFile(j).c_str(), namelength);
            }
            size = fb->getSize();
            writeToSocket(dist_fd, &size, sizeof(int));
            writeToSocket(dist_fd, fb->buf, size);
          }
          writeToSocket(dist_fd, &fi->startdepth, sizeof(int));
          int depth = config->getDepth();
          writeToSocket(dist_fd, &depth, sizeof(int));
          unsigned int alarm = config->getAlarm();
          writeToSocket(dist_fd, &alarm, sizeof(int));
          unsigned int tracegrindAlarm = config->getTracegrindAlarm();
          writeToSocket(dist_fd, &tracegrindAlarm, sizeof(int));
          int threads = config->getSTPThreads();
          writeToSocket(dist_fd, &threads, sizeof(int));

          int progArgsNum = config->getProgAndArg().size();
          writeToSocket(dist_fd, &progArgsNum, sizeof(int));

          bool leaks = config->checkForLeaks();
          writeToSocket(dist_fd, &leaks, sizeof(bool));
          bool traceChildren = config->getTraceChildren();
          writeToSocket(dist_fd, &traceChildren, sizeof(bool));
          bool checkDanger = config->getCheckDanger();
          writeToSocket(dist_fd, &checkDanger, sizeof(bool));
          bool debug = config->getDebug();
          writeToSocket(dist_fd, &debug, sizeof(bool));
          bool verbose = config->getVerbose();
          writeToSocket(dist_fd, &verbose, sizeof(bool));
          bool programOutput = config->getProgramOutput();
          writeToSocket(dist_fd, &programOutput, sizeof(bool));
          bool networkLog = config->getNetworkLog();
          writeToSocket(dist_fd, &networkLog, sizeof(bool));
          bool suppressSubcalls = config->getSuppressSubcalls();
          writeToSocket(dist_fd, &suppressSubcalls, sizeof(bool));
          bool STPThreadsAuto = config->getSTPThreadsAuto();
          writeToSocket(dist_fd, &STPThreadsAuto, sizeof(bool));

          if (sockets)
          {
            string host = config->getHost();
            int length = host.length();
            writeToSocket(dist_fd, &length, sizeof(int));
            writeToSocket(dist_fd, host.c_str(), length);
            unsigned int port = config->getPort();
            writeToSocket(dist_fd, &port, sizeof(int));
          }
          
          {
            string plugin_name = config->getPlugin();
            int length = plugin_name.length();
            writeToSocket(dist_fd, &length, sizeof(int));
            writeToSocket(dist_fd, plugin_name.c_str(), length);
          }

          if (config->getInputFilterFile() != "")
          {
            FileBuffer *mask;
            try
            {
              mask = new FileBuffer(config->getInputFilterFile());
              size = mask->getSize();
            }
            catch (const char*)
            {
              size = 0;
            }
            writeToSocket(dist_fd, &size, sizeof(int));
            if (size > 0)
            {
              writeToSocket(dist_fd, mask->buf, size);
            }
          }
          else
          {
            int z = 0;
            writeToSocket(dist_fd, &z, sizeof(int));
          }

          int funcFilters = config->getFuncFilterUnitsNum();
          writeToSocket(dist_fd, &funcFilters, sizeof(int));
          for (int i = 0; i < config->getFuncFilterUnitsNum(); i++)
          {
            string f = config->getFuncFilterUnit(i);
            int length = f.length();
            writeToSocket(dist_fd, &length, sizeof(int));
            writeToSocket(dist_fd, f.c_str(), length);
          }
          if (config->getFuncFilterFile() != "")
          {
            FileBuffer *filter;
            try
            {
              filter = new FileBuffer(config->getFuncFilterFile());
              size = filter->getSize();
            }
            catch (const char*)
            {
              size = 0;
            }
            writeToSocket(dist_fd, &size, sizeof(int));
            if (size > 0)
            {
              writeToSocket(dist_fd, filter->buf, size);
            }
          }
          else
          {
            int z = 0;
            writeToSocket(dist_fd, &z, sizeof(int));
          }
          if (config->getAgentDir() != string(""))
          {
             string agentDir = config->getAgentDir();
             int length = agentDir.length();
             writeToSocket(dist_fd, &length, sizeof(int));
             writeToSocket(dist_fd, agentDir.c_str(), length);
          }
          else
          {
            int length = 0;
            writeToSocket(dist_fd, &length, sizeof(int));
          }
          for (vector<string>::const_iterator it = config->getProgAndArg().begin(); it != config->getProgAndArg().end(); it++)
          {
            int argsSize = it->length();
            writeToSocket(dist_fd, &argsSize, sizeof(int));
            writeToSocket(dist_fd, it->c_str(), argsSize);
          }
          if (it->second != initial)
          {
            delete it->second;
          }
          inputs.erase(it);
          response_num--;
        }
        while (response_num > 0)
        {
          int tosend = 0;
          writeToSocket(dist_fd, &tosend, sizeof(int));
          response_num--;
        }
      }
      else if (c == 'g')
      {
        writeToSocket(dist_fd, "r", 1);
        //sending "r"(responding) before data - this is to have something different from "q", so that server
        //can understand that main avalanche finished normally
        readFromSocket(dist_fd, &response_num, sizeof(int));
        while (response_num > 0)
        {
          if (inputs.size() <= limit)
          { 
            break;
          }
          LOG(Logger::NETWORK_LOG, "Sending input.");
          multimap<Key, Input*, cmp>::iterator it = --inputs.end();
          it--;
          Input* fi = it->second;
          for (int j = 0; j < fi->files.size(); j ++)
          {
            FileBuffer* fb = fi->files.at(j);
            size = fb->getSize();
            writeToSocket(dist_fd, &size, sizeof(int));
            writeToSocket(dist_fd, fb->buf, size);
          }
          writeToSocket(dist_fd, &fi->startdepth, sizeof(int));
          if (it->second != initial)
          {
            delete it->second;
          }
          inputs.erase(it);
          response_num--;
        }
        while (response_num > 0)
        {
          int tosend = 0;
          writeToSocket(dist_fd, &tosend, sizeof(int));
          response_num--;
        }
      }
      else
      {
        int tosend = 0;
        writeToSocket(dist_fd, &tosend, sizeof(int));
      }
      FD_ZERO(&readfds);
      FD_SET(dist_fd, &readfds);
      select(dist_fd + 1, &readfds, NULL, NULL, &timer);      
    }
  }
  catch (const char* msg)
  {
    LOG(Logger::NETWORK_LOG, "Connection with server lost.");
    LOG(Logger::NETWORK_LOG, "Continuing work in local mode.");
    is_distributed = false;
  }
}

ExecutionManager::~ExecutionManager()
{
//    LOG(Logger::DEBUG, "Destructing plugin manager.");

    if (is_distributed)
    {
        write(dist_fd, "q", 1);
        shutdown(dist_fd, SHUT_RDWR);
        close(dist_fd);
    }
    
    if (config->getRemoteValgrind() != "")
    {
        kind = UNID;
        write(remote_fd, &kind, sizeof(int));
        close(remote_fd);
    }

    if (thread_num > 0)
    {
        pthread_mutex_destroy(&add_inputs_mutex);
        pthread_mutex_destroy(&add_exploits_mutex);
        pthread_mutex_destroy(&add_bb_mutex);
        pthread_mutex_destroy(&finish_mutex);
        pthread_mutex_destroy(&add_remote_mutex);
        pthread_cond_destroy(&input_available_cond);
    }

    delete config;
}
