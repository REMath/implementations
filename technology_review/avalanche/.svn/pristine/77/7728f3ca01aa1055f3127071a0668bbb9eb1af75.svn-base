/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*----------------------- Simple agent for distributed Avalanche. ------------------------*/
/*------------------------------------- agent.cpp ----------------------------------------*/
/*----------------------------------------------------------------------------------------*/

/*
   Copyright (C) 2010 Ildar Isaev
      iisaev@ispras.ru
   Copyright (C) 2010 Michael Ermakov
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
 
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>

#include <vector>
#include <string>

#include "util.h"

#define PERM_R_W S_IRUSR | S_IROTH | S_IRGRP | \
                 S_IWUSR | S_IWOTH | S_IWGRP

using namespace std;

int fd;
pid_t pid = 0;
vector <char*> file_name;
int file_num;
bool sockets, datagrams;

void recvInput(bool initial)
{
  int net_fd, length, namelength;
  if (sockets || datagrams)
  {
    net_fd = open("replace_data", O_WRONLY | O_CREAT | O_TRUNC, PERM_R_W);
    write(net_fd, &file_num, sizeof(int));
  }
  for (int j = 0; j < file_num; j ++)
  {
    if (initial && !sockets && !datagrams)
    {
      readFromSocket(fd, &namelength, sizeof(int));
      if (namelength == -1)
      {
        writeToSocket(fd, &namelength, sizeof(int));
        throw "main Avalanche agent is finished";
      }
      char* filename = new char[namelength + 1];
      readFromSocket(fd, filename, namelength);
      filename[namelength] = '\0';
      if (strstr(filename, "argv.log") != NULL)
      {
        delete []filename;
        filename = strdup("argv.log");
      }
      file_name.push_back(filename);
    }
    readFromSocket(fd, &length, sizeof(int));
    if (length == -1)
    {
      writeToSocket(fd, &length, sizeof(int));
      throw "main Avalanche agent is finished";
    }
    char* file = new char[length];
    readFromSocket(fd, file, length);
    if (sockets || datagrams)
    {
      write(net_fd, &length, sizeof(int));
      write(net_fd, file, length);
    }
    else
    {
      int descr = open(file_name.at(j), O_WRONLY | O_CREAT, PERM_R_W);
      if (descr == -1)
      {
        perror("open failed");
        close(fd);
        //exit(EXIT_FAILURE);
      }
      write(descr, file, length);
      close(descr);
    }
    delete[] file;
  }
  if (sockets || datagrams)
  {
    close(net_fd);
  }
}

void sig_hndlr(int signo)
{
  int startdepth = 0;
  int descr = open("startdepth.log", O_WRONLY | O_CREAT, PERM_R_W);
  writeToSocket(fd, "g", 1);
  try
  {
    recvInput(false);
    readFromSocket(fd, &startdepth, sizeof(int));
  }
  catch (const char* msg)
  {
    shutdown(fd, O_WRONLY);
    close(fd);
    printf("coudln't receive non zero scored input: %s\n", msg);
  }
  write(descr, &startdepth, sizeof(int));
  close(descr);
  
  kill(pid, SIGUSR2);
}

void int_handler(int signo)
{
  shutdown(fd, SHUT_RDWR);
  close(fd);
  if (pid != 0)
  {
    kill(pid, SIGINT);
  }
  for (int i = 0; i < file_name.size(); i ++)
  {
    delete [](file_name.at(i));
  }
  file_name.clear();
}  
 
int main(int argc, char** argv)
{
  bool requestNonZero = false;
  if ((argc < 3) || (argc > 4))
  {
    printf("usage: av-agent <host address> <port number> [--request-non-zero]\n");
    exit(EXIT_FAILURE);
  }
  if (argc == 4)
  {
    if (!strcmp(argv[3], "--request-non-zero"))
    {
      requestNonZero = true;
    }
    else
    {
      printf("usage: av-agent <host address> <port number> [--request-non-zero]\n");
      exit(EXIT_FAILURE);
    }
  }

  int port = atoi(argv[2]);
  if (port == 0)
  {
    printf("usage: av-agent <host address> <port number> [--request-non-zero]\n");
    exit(EXIT_FAILURE);
  }
 
  struct sockaddr_in stSockAddr;
  memset(&stSockAddr, 0, sizeof(struct sockaddr_in));
  stSockAddr.sin_family = AF_INET;
  stSockAddr.sin_port = htons(port);
  int res = inet_pton(AF_INET, argv[1], &stSockAddr.sin_addr);
 
  if (res <= 0)
  {
    perror("wrong network address");
    printf("usage: av-agent <host address> <port number> [--request-non-zero]\n");
    exit(EXIT_FAILURE);
  }

  fd = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
  if (fd == -1)
  {
    perror("cannot create socket");
    exit(EXIT_FAILURE);
  }
    
  res = connect(fd, (const struct sockaddr*)&stSockAddr, sizeof(struct sockaddr_in));
  if (res < 0)
  {
    perror("error connect failed");
    close(fd);
    exit(EXIT_FAILURE);
  }  

  printf("connected to distribution server\n");
  int runs = 0;

  try
  {
    signal(SIGINT, int_handler);
    writeToSocket(fd, "a", 1);

    int namelength, length, startdepth, invertdepth, alarm, tracegrindAlarm, pluginlength;
    int threads, argsnum, masklength, filtersNum, flength, received, net_fd;
    bool useMemcheck, leaks, traceChildren, checkDanger, verbose, debug, programOutput, networkLog, suppressSubcalls, STPThreadsAuto;
    string plugin_name;
  
    readFromSocket(fd, &file_num, sizeof(int));
    if (file_num == -1)
    {
      writeToSocket(fd, &file_num, sizeof(int));
      throw "main Avalanche agent is finished";
    }
    readFromSocket(fd, &sockets, sizeof(bool));
    readFromSocket(fd, &datagrams, sizeof(bool));
    recvInput(true);

    readFromSocket(fd, &startdepth, sizeof(int));
    readFromSocket(fd, &invertdepth, sizeof(int));
    readFromSocket(fd, &alarm, sizeof(int));
    readFromSocket(fd, &tracegrindAlarm, sizeof(int));
    readFromSocket(fd, &threads, sizeof(int));
    readFromSocket(fd, &argsnum, sizeof(int));
    readFromSocket(fd, &leaks, sizeof(bool));
    readFromSocket(fd, &traceChildren, sizeof(bool));
    readFromSocket(fd, &checkDanger, sizeof(bool));
    readFromSocket(fd, &debug, sizeof(bool));
    readFromSocket(fd, &verbose, sizeof(bool));
    readFromSocket(fd, &programOutput, sizeof(bool));
    readFromSocket(fd, &networkLog, sizeof(bool));
    readFromSocket(fd, &suppressSubcalls, sizeof(bool));
    readFromSocket(fd, &STPThreadsAuto, sizeof(bool));
 
    char* avalanche_argv[100];
    string argstr(argv[0]);
    size_t sl = argstr.find_last_of('/');
    if (sl != string::npos) 
    {
      avalanche_argv[0] = strdup((char*) (argstr.substr(0, sl + 1) + string("avalanche")).c_str());
    }
    else 
    {
      avalanche_argv[0] = "avalanche";
    }
    argstr.clear();
    int argv_delta = 0;

    if (!sockets && !datagrams)
    {
      for (int i = 0; i < file_num; i ++)
      {
        char s[512];
        sprintf(s, "--filename=%s", file_name.at(i));
        avalanche_argv[1 + i] = strdup(s);
      }
      argv_delta = file_num;
    }
  
    char depth[128];
    sprintf(depth, "--depth=%d", invertdepth);
    avalanche_argv[1 + argv_delta] = depth;

    char sdepth[128];
    sprintf(sdepth, "--startdepth=%d", startdepth);
    avalanche_argv[2 + argv_delta] = sdepth;

    char alrm[128];
    sprintf(alrm, "--alarm=%d", alarm);
    avalanche_argv[3 + argv_delta] = alrm;

    avalanche_argv[4 + argv_delta] = "--prefix=branch0_";

    if (STPThreadsAuto)
    {
      avalanche_argv[5 + argv_delta] = "--stp-threads=auto";
    }
    else
    {
      char thrds[128];
      sprintf(thrds, "--stp-threads=%d", threads);
      avalanche_argv[5 + argv_delta] = strdup(thrds);
    }

    avalanche_argv[6 + argv_delta] = "--report-log=report0.log";
    int av_argc = 7 + argv_delta;

    if (requestNonZero)
    {
      avalanche_argv[7 + argv_delta] = "--agent";
      av_argc++;
    }

    if (tracegrindAlarm != 0)
    {
      char alrm[128];
      sprintf(alrm, "--tracegrind-alarm=%d", tracegrindAlarm);
      avalanche_argv[av_argc++] = alrm;
    }
    if (leaks)
    {
      avalanche_argv[av_argc++] = "--leaks";
    }
    if (traceChildren)
    {
      avalanche_argv[av_argc++] = "--trace-children";
    }
    if (checkDanger)
    {
      avalanche_argv[av_argc++] = "--check-danger";
    }
    if (debug)
    {
      avalanche_argv[av_argc++] = "--debug";
    }
    if (verbose)
    {
      avalanche_argv[av_argc++] = "-v";
    }
    if (programOutput)
    {
      avalanche_argv[av_argc++] = "--program-output";
    }
    if (networkLog)
    {
      avalanche_argv[av_argc++] = "--network-log";
    }
    if (sockets)
    {
      avalanche_argv[av_argc++] = "--sockets";
    }
    if (datagrams)
    {
      avalanche_argv[av_argc++] = "--datagrams";
    }
    if (suppressSubcalls)
    {
      avalanche_argv[av_argc++] = "--suppress-subcalls";
    }

    if (sockets)
    {
      int length, port;
      char buf[128], host[128], prt[128];
      readFromSocket(fd, &length, sizeof(int));
      readFromSocket(fd, buf, length);
      buf[length] = '\0';
      sprintf(host, "--host=%s", buf);
      avalanche_argv[av_argc++] = strdup(host);
      readFromSocket(fd, &port, sizeof(int));
      sprintf(prt, "--port=%d", port);
      avalanche_argv[av_argc++] = strdup(prt);
    }
    
    {
      char buf[128], plugin_name[128];
      readFromSocket(fd, &pluginlength, sizeof(int));
      readFromSocket(fd, buf, pluginlength);
      buf[pluginlength] = '\0';
      sprintf(plugin_name, "--tool=%s", buf);
      avalanche_argv[av_argc++] = strdup(plugin_name);
    }
    
    readFromSocket(fd, &masklength, sizeof(int));
    if (masklength != 0)
    {
      char* mask = new char[masklength];
      readFromSocket(fd, mask, masklength);
      int descr = open("mask", O_WRONLY | O_CREAT | O_TRUNC, PERM_R_W);
      if (descr == -1)
      {
        perror("open failed");
        close(fd);
        exit(EXIT_FAILURE);
      }
      write(descr, mask, masklength);
      close(descr);
      delete[] mask;
      avalanche_argv[av_argc++] = "--mask=mask";
    }

    readFromSocket(fd, &filtersNum, sizeof(int));
    for (int i = 0; i < filtersNum; i++)
    {
      int length;
      char buf[128], fltr[128];
      readFromSocket(fd, &length, sizeof(int));
      readFromSocket(fd, buf, length);
      buf[length] = '\0';
      sprintf(fltr, "--func-name=%s", buf);
      avalanche_argv[av_argc++] = fltr;
    } 

    readFromSocket(fd, &flength, sizeof(int));
    if (flength != 0)
    {
      char* filter = new char[flength];
      readFromSocket(fd, filter, flength);
      int descr = open("filter", O_WRONLY | O_CREAT | O_TRUNC, PERM_R_W);
      if (descr == -1)
      {
        perror("open failed");
        close(fd);
        exit(EXIT_FAILURE);
      }
      write(descr, filter, flength);
      close(descr);
      delete[] filter;
      avalanche_argv[av_argc++] = "--func-file=filter";
    }

    readFromSocket(fd, &length, sizeof(int));
    if (length != 0)
    {
      char* resultDir = new char[length + 1];
      readFromSocket(fd, resultDir, length);
      resultDir[length] = '\0';
      char buf[256];
      sprintf(buf, "--result-dir=%s", resultDir);
      avalanche_argv[av_argc++] = strdup(buf);
    }

    for (int i = 0; i < argsnum; i++)
    {
      int arglength;
      readFromSocket(fd, &arglength, sizeof(int));
      char* arg = new char[arglength + 1];
      readFromSocket(fd, arg, arglength);
      arg[arglength] = '\0';
      avalanche_argv[av_argc++] = arg;
    }
    avalanche_argv[av_argc] = NULL;
    
    for (;;)
    {
      signal(SIGUSR1, sig_hndlr);
      pid = fork();
      if (pid == 0)
      {
        printf("starting child avalanche...\n");
        execvp(avalanche_argv[0], avalanche_argv);
      }
      wait(NULL);

      writeToSocket(fd, "g", 1);
      recvInput(false);
    
      int startdepth;
      readFromSocket(fd, &startdepth, sizeof(int));

      char sdepth[128];
      sprintf(sdepth, "--startdepth=%d", startdepth);
      avalanche_argv[2 + argv_delta] = sdepth;

      char prefix[128];
      sprintf(prefix, "--prefix=branch%d_", ++runs);
      avalanche_argv[4 + argv_delta] = prefix; 

      char report[128];
      sprintf(report, "--report-log=report%d.log", runs);
      avalanche_argv[6 + argv_delta] = report; 
    }
  }
  catch (const char* msg)
  {
    shutdown(fd, SHUT_RDWR);
    close(fd);
    printf("exiting...\n");
  }

  printf("Exploits report:\n");
  for (int i = 0; i <= runs; i++)
  {
    char report[128];
    sprintf(report, "report%d.log", i);
    int fd = open(report, O_RDONLY, PERM_R_W);
    if (fd != -1)
    {
      struct stat fileInfo;
      fstat(fd, &fileInfo);
      int size = fileInfo.st_size;
      char* buf = new char [size];
      read(fd, buf, size);
      char branch[128];
      int s = sprintf(branch, "branch%d:\n", i);
      write(1, branch, s);
      write(1, buf, size);
      close(fd);
      unlink(report);
      delete[] buf;
    }
  }
  for (int i = 0; i < file_name.size(); i ++)
  {
    delete [](file_name.at(i));
  }
  file_name.clear();
  unlink("argv.log");
  return 0;
}

