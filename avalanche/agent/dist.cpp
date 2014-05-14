/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*---------------------- Simple server for distributed Avalanche. ------------------------*/
/*-------------------------------------- dist.cpp ----------------------------------------*/
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
#include <netinet/in.h>
#include <arpa/inet.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <signal.h>

#include <algorithm>
#include <vector>
#include <set>

#include "util.h"

//#define DEBUG

using namespace std;

vector<int> fds;
int sfd;
int mainfd = -1;

set<int> starvating_a;
set<int> starvating_g;

void finalize_and_exit()
{
  fds.erase(find(fds.begin(), fds.end(), mainfd));

  for (set<int>::iterator fd = starvating_a.begin(); fd != starvating_a.end(); fd++)
  {
    int tosend = -1;
    try
    {
      writeToSocket(*fd, &tosend, sizeof(int));
      readFromSocket(*fd, &tosend, sizeof(int));
    }
    catch (...)
    {  
      printf("connection with %d is down\n", *fd); 
    }    
    shutdown(*fd, SHUT_RDWR);
    close(*fd);
    fds.erase(find(fds.begin(), fds.end(), *fd));
  }
  for (set<int>::iterator fd = starvating_g.begin(); fd != starvating_g.end(); fd++)
  {
    int tosend = -1;
    try
    {
      writeToSocket(*fd, &tosend, sizeof(int));
      readFromSocket(*fd, &tosend, sizeof(int));
    }
    catch (...)
    { 
      printf("connection with %d is down\n", *fd); 
    }  
    shutdown(*fd, SHUT_RDWR);
    close(*fd);
    fds.erase(find(fds.begin(), fds.end(), *fd));
  }
  while (fds.size() > 0)
  {
    fd_set readfds;
    int max_d = 0;
    FD_ZERO(&readfds);

    for (vector<int>::iterator fd = fds.begin(); fd != fds.end(); fd++)
    {
      FD_SET(*fd, &readfds);
      if (*fd > max_d) 
      {
        max_d = *fd;
      }
    }

    select(max_d + 1, &readfds, NULL, NULL, NULL);

    for (vector<int>::iterator fd = fds.begin(); fd != fds.end();)
    {
      if (FD_ISSET(*fd, &readfds)) 
      {
        try
        {
          int tosend = -1;
          writeToSocket(*fd, &tosend, sizeof(int));
          readFromSocket(*fd, &tosend, sizeof(int));
        }
        catch (...) 
        { 
     
        }
        shutdown(*fd, SHUT_RDWR);
        close(*fd);
        vector<int>::iterator to_erase = fd; 
        fd++;
        if (fd == fds.end())
        {
          fds.erase(to_erase);
          break;
        }
        fds.erase(to_erase);
      }
      else
      {
        fd++;
      }
    }
  }

  shutdown(mainfd, SHUT_RDWR);
  close(mainfd);
  shutdown(sfd, SHUT_RDWR);
  close(sfd);
  exit(0);
}

void pass(int fd, void* valaddr, size_t size)
{
  try
  {
    readFromSocket(mainfd, valaddr, size);
  }
  catch (const char* msg) 
  { 
    printf("connection with main avalanche is down\n"); 
    finalize_and_exit(); 
  } 
  try
  { 
    writeToSocket(fd, valaddr, size);
  }
  catch (const char* msg) 
  { 
    printf("connection with %d is down\n", fd); 
    fds.erase(find(fds.begin(), fds.end(), fd)); 
  }
}

void pass(int fd, int length)
{
  char* buf = new char[length];
  try
  {
    readFromSocket(mainfd, buf, length);
  }
  catch (const char* msg) 
  { 
    printf("connection with main avalanche is down\n"); 
    finalize_and_exit(); 
  } 
  try
  { 
    writeToSocket(fd, buf, length);
  }
  catch (const char* msg) 
  { 
    printf("connection with %d is down\n", fd); 
    fds.erase(find(fds.begin(), fds.end(), fd)); 
  }
  delete[] buf;
}

void sig_handler(int signo)
{
  shutdown(sfd, SHUT_RDWR);
  close(sfd);
  for (int i = 0; i < fds.size() && fds.at(i) != mainfd; i ++)
  {
    close(fds.at(i));
  }
  exit(0);
}
 
int main(int argc, char** argv)
{
  if (argc != 2)
  {
    printf("usage: av-dist <port number>\n");
    exit(EXIT_FAILURE);
  }    
  int port = atoi(argv[1]);
  if (port == 0)
  {
    printf("usage: av-dist <port number>\n");
    exit(EXIT_FAILURE);
  }

  struct sockaddr_in stSockAddr;
  sfd = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
  if(sfd == -1)
  {
    perror("can not create socket");
    exit(EXIT_FAILURE);
  }

  int on = 1;
  setsockopt(sfd, SOL_SOCKET, SO_REUSEADDR, &on, sizeof(on));
  signal(SIGINT, sig_handler);
 
  memset(&stSockAddr, 0, sizeof(struct sockaddr_in));
  stSockAddr.sin_family = AF_INET;  
  stSockAddr.sin_port = htons(port);
  stSockAddr.sin_addr.s_addr = INADDR_ANY;

  int bindRes = bind(sfd, (const struct sockaddr*)&stSockAddr, sizeof(struct sockaddr_in));
  if(bindRes == -1)
  {
    perror("error bind failed");
    close(sfd);
    exit(EXIT_FAILURE);
  }

  int listenRes = listen(sfd, 10);
  if(listenRes == -1)
  {
    perror("error listen failed");
    close(sfd);
    exit(EXIT_FAILURE);
  }

  bool gameBegan = false;
  int filenum;
  bool sockets, datagrams;
 
  for(;;)
  {
    fd_set readfds;
    int max_d = sfd;
    FD_ZERO(&readfds);
    FD_SET(sfd, &readfds);

    for (vector<int>::iterator fd = fds.begin(); fd != fds.end(); fd++)
    {
      FD_SET(*fd, &readfds);
      if (*fd > max_d) 
      {
        max_d = *fd;
      }
    }

    if (gameBegan)
    {
#ifdef DEBUG 
      printf("iterating through starvated\n");
#endif
      int size = starvating_a.size();
      if (size > 0)
      {
        char c = 'q';
        try
        {
          writeToSocket(mainfd, "a", 1);
          writeToSocket(mainfd, &size, sizeof(int));
          readFromSocket(mainfd, &c, 1);
        }
        catch (...)
        { 
          printf("connection with main avalanche is down\n"); 
          finalize_and_exit();
        }          
        //first read 1 byte - either "r" or "q"
        if (c == 'q')
        {
          printf("main avalanche finished work\n");
          finalize_and_exit();
        }
        for (set<int>::iterator fd = starvating_a.begin(); fd != starvating_a.end();)
        {
          int namelength, length, startdepth, invertdepth, alarm, tracegrindAlarm, threads, dirLength, pluginlength;
          int argsnum, filtersNum, filterlength, masklength;
          bool useMemcheck, leaks, traceChildren, checkDanger, verbose, debug, programOutput, networkLog, suppressSubcalls, STPThreadsAuto;
          filenum = 0;
          try 
          { 
            readFromSocket(mainfd, &filenum, sizeof(int)); 
          } 
          catch (const char* msg) 
          { 
            printf("connection with main avalanche is down\n"); 
            finalize_and_exit(); 
          }
#ifdef DEBUG 
          printf("filenum=%d\n", filenum);
#endif
          if (filenum > 0)
          {
            try
            {
              writeToSocket(*fd, &filenum, sizeof(int));
            }
            catch (...)
            {
              printf("connection with %d is down\n", *fd);
              fds.erase(find(fds.begin(), fds.end(), *fd));
            }  
            pass(*fd, &sockets, sizeof(bool));
            pass(*fd, &datagrams, sizeof(bool));
            for (int j = 0; j < filenum; j ++)
            {
              if (!sockets && !datagrams)
              {
                pass(*fd, &namelength, sizeof(int));
                pass(*fd, namelength);
              }
              pass(*fd, &length, sizeof(int));
              pass(*fd, length);
            }
            pass(*fd, &startdepth, sizeof(int));
            pass(*fd, &invertdepth, sizeof(int));
            pass(*fd, &alarm, sizeof(int));
            pass(*fd, &tracegrindAlarm, sizeof(int));
            pass(*fd, &threads, sizeof(int));
            pass(*fd, &argsnum, sizeof(int));
            pass(*fd, &leaks, sizeof(bool));
            pass(*fd, &traceChildren, sizeof(bool));
            pass(*fd, &checkDanger, sizeof(bool));
            pass(*fd, &debug, sizeof(bool));
            pass(*fd, &verbose, sizeof(bool));
            pass(*fd, &programOutput, sizeof(bool));
            pass(*fd, &networkLog, sizeof(bool));
            pass(*fd, &suppressSubcalls, sizeof(bool));
            pass(*fd, &STPThreadsAuto, sizeof(bool));

            if (sockets)
            {
              int length, port;
              pass(*fd, &length, sizeof(int));
              pass(*fd, length);
              pass(*fd, &port, sizeof(int));
            }
            pass(*fd, &pluginlength, sizeof(int));
            printf("%d\n", pluginlength);
            pass(*fd, pluginlength);

            pass(*fd, &masklength, sizeof(int));
            if (masklength != 0)
            {
              pass(*fd, masklength);
            }

            pass(*fd, &filtersNum, sizeof(int));
            for (int i = 0; i < filtersNum; i++)
            {
              int length; 
              pass(*fd, &length, sizeof(int));
              pass(*fd, length);
            }

            pass(*fd, &filterlength, sizeof(int));
            if (filterlength != 0)
            {
              pass(*fd, filterlength);
            }
 
            pass(*fd, &dirLength, sizeof(int));
            if (dirLength != 0)
            {
              pass(*fd, dirLength);
            }

            for (int i = 0; i < argsnum; i++)
            {
              int arglength;
              pass(*fd, &arglength, sizeof(int));
              pass(*fd, arglength);
            }
            set<int>::iterator to_erase = fd;
            fd++;
            if (fd == starvating_a.end())
            {
              starvating_a.erase(to_erase);
              break;
            }
            starvating_a.erase(to_erase);
          }
          else
          {
            fd++;
          }
        }
      }

      size = starvating_g.size();
      if (size > 0)
      {
        int length, startdepth;
        char c = 'q';
        try
        {
          writeToSocket(mainfd, "g", 1);
          writeToSocket(mainfd, &size, sizeof(int));
          readFromSocket(mainfd, &c, 1);
        }
        catch (...)
        { 
          printf("connection with main avalanche is down\n"); 
          finalize_and_exit();
        } 
        //first read 1 byte - either "r" or "q"
        if (c == 'q')
        {
          printf("main avalanche finished work\n");
          finalize_and_exit();
        }
        for (set<int>::iterator fd = starvating_g.begin(); fd != starvating_g.end();)
        {
          for (int j = 0; j < filenum; j ++)
          {
            try 
            { 
              readFromSocket(mainfd, &length, sizeof(int)); 
            } 
            catch (const char* msg) 
            { 
              printf("connection with main avalanche is down\n"); 
              finalize_and_exit(); 
            }
            if (length > 0)
            {
              try
              {
                writeToSocket(*fd, &length, sizeof(int));
              }
              catch (...)
              {
                printf("connection with %d is down\n", *fd);
                fds.erase(find(fds.begin(), fds.end(), *fd));
              }                
              pass(*fd, length);
            }
            else 
            {
              break;
            }
          }
          if (length > 0)
          {
            pass(*fd, &startdepth, sizeof(int));
            set<int>::iterator to_erase = fd;
            fd++;
            if (fd == starvating_g.end())
            {
              starvating_g.erase(to_erase);
              break;
            }
            starvating_g.erase(to_erase);
          }
          else
          {
            fd++;
          }
        }
      }
    }

#ifdef DEBUG 
    printf("selecting...\n");
#endif
    int res;
    if ((starvating_a.size() == 0) && (starvating_g.size() == 0) || !gameBegan)
    {
      res = select(max_d + 1, &readfds, NULL, NULL, NULL);
    }
    else
    {
      struct timeval timer;
      timer.tv_sec = 0;
      timer.tv_usec = 0;
      res = select(max_d + 1, &readfds, NULL, NULL, &timer);
    }
#ifdef DEBUG 
    printf("done\n");
#endif
    if (res == -1) 
    {
      FD_ZERO(&readfds);
      perror("select failed");
    }

    if (FD_ISSET(sfd, &readfds)) 
    {
      int cfd = accept(sfd, NULL, NULL);
      if (cfd < 0)
      {
        perror("error accept failed");
        close(sfd);
        exit(EXIT_FAILURE);
      }
      fds.push_back(cfd); 
      printf("connection with %d is set up\n", cfd);
    }

#ifdef DEBUG 
    printf("iterating through sockets...\n");
#endif
    vector<int> to_erase;
    for (vector<int>::iterator fd = fds.begin(); fd != fds.end(); fd++)
    {
      //printf("103\n");
      if (FD_ISSET(*fd, &readfds)) 
      {
        //printf("106\n");
        char command;
        try 
        { 
          readFromSocket(*fd, &command, 1); 
        } 
        catch (const char* msg) 
        { 
          if (*fd == mainfd)
          {
            printf("connection with main avalanche is down\n"); 
            finalize_and_exit(); 
          }
          else
          {
            printf("connection with %d is down\n", *fd);
            to_erase.push_back(*fd);
            continue;
          }
        }
        if (command == 'm') 
        {
#ifdef DEBUG 
          printf("received m\n");
#endif
          mainfd = *fd;
          gameBegan = true;
          int size = fds.size();
          try 
          { 
            writeToSocket(mainfd, &size, sizeof(int)); 
          } 
          catch (const char* msg) 
          { 
            printf("connection with main avalanche is down\n"); 
            finalize_and_exit(); 
          }
        }
        else if (command == 'q')
        {
          printf("main avalanche finished work\n");
          finalize_and_exit();
        }
        else if (command == 'g')
        {
#ifdef DEBUG 
          printf("added %d to starvated_g\n", *fd);
#endif
          starvating_g.insert(*fd);
        }         
        else //game not began
        {
#ifdef DEBUG 
          printf("added %d to starvated_a\n", *fd);
#endif
          starvating_a.insert(*fd);
        }
      }
    }
    for (vector<int>::iterator fd = to_erase.begin(); fd != to_erase.end(); fd ++)
    {
      fds.erase(find(fds.begin(), fds.end(), *fd));
      starvating_a.erase(*fd);
      starvating_g.erase(*fd);
    }
  }
  for (int i = 0; i < fds.size() && fds.at(i) != mainfd; i ++)
  {
    close(fds.at(i));
  }
  close(mainfd);
  close(sfd);
  return 0;
}

