/*---------------------------------------------------------------------------*/
/*------------------------------- AVALANCHE ---------------------------------*/
/*- Driver. Coordinates other processes, traverses conditional jumps tree. --*/
/*----------------------- RemotePluginExecutor.cpp --------------------------*/
/*---------------------------------------------------------------------------*/
 
/*
   Copyright (C) 2011 Michael Ermakov
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

#include <cerrno>
#include <cstring>
#include <cstdlib>
#include <unistd.h>
#include <fcntl.h>

#include "Logger.h"
#include "RemotePluginExecutor.h"
#include "FileBuffer.h"
#include "ExecutionManager.h"

using namespace std;

static Logger *logger = Logger::getLogger();

static
void writeToSocket(int fd, const void* b, size_t count)
{
    char* buf = (char*) b;
    size_t sent = 0;
    while (sent < count)
    {
        size_t s = write(fd, buf + sent, count - sent);
        if (s < 1)
        {
            throw "connection is down";
        }
        sent += s;
    }
}

static
void readFromSocket(int fd, const void* b, size_t count)
{
    char* buf = (char*) b;
    size_t received = 0;
    while (received < count)
    {
        size_t r = read(fd, buf + received, count - received);
        if (r < 1)
        {
            throw "net";
        }
        received += r;
    }
}

#define CHUNK_SIZE 32

static
void readFileFromSocket(int fd, string file_name)
{
    int file_fd, length;
    size_t received = 0, r;
    char buf[CHUNK_SIZE];
    readFromSocket(fd, &length, sizeof(int));
    file_fd = open(file_name.c_str(), O_CREAT | O_TRUNC | O_WRONLY, PERM_R_W);
    if (file_fd == -1)
    {
        LOG(Logger::ERROR, "Cannot open file " << file_name <<
                           ": " << strerror(errno));
        throw "local";
    }
    while(received < length)
    {
        if (length - received > CHUNK_SIZE)
        {
            r = read(fd, buf, CHUNK_SIZE);
        }
        else
        {
            r = read(fd, buf, length - received);
        }
        if (r < 1)
        {
            close(file_fd);
            throw "net";
        }
        received += r;
        r = write(file_fd, buf, r);
        if (r < 1)
        {
            LOG(Logger::ERROR, "Cannot write to file " << file_name <<
                               ": " << strerror(errno));
            close(file_fd);
            throw "local";
        }
    }
    close(file_fd);
}

static
void writeFileToSocket(int fd, string file_name)
{
    int file_fd;
    size_t sent = 0, r;
    char buf[CHUNK_SIZE];
    file_fd = open(file_name.c_str(), O_RDONLY, S_IRUSR);
    if (file_fd == -1)
    {
        LOG(Logger::ERROR, "Cannot open file " << file_name <<
                           ": " << strerror(errno));
        throw "local";
    }
    struct stat f_stat;
    if (fstat(file_fd, &f_stat) == -1)
    {
        LOG(Logger::ERROR, strerror(errno));
        throw "local";
    }
    writeToSocket(fd, &(f_stat.st_size), sizeof(int));
    while(sent < f_stat.st_size)
    {
        if (f_stat.st_size - sent > CHUNK_SIZE)
        {
            r = read(file_fd, buf, CHUNK_SIZE);
        }
        else
        {
            r = read(file_fd, buf, f_stat.st_size - sent);
        }
        if (r < 1)
        {
            LOG(Logger::ERROR, "Cannot read from file " << file_name <<
                               ": " << strerror(errno));
            throw "local";
        }
        sent += r;
        r = write(fd, buf, r);
        if (r < 1)
        {
            throw "net";
        }
    }
}

#undef CHUNK_SIZE

static
void readTraceOnTheRun(int fd, string temp_dir)
{
    int file_fd[2];
    int length;
    readFromSocket(fd, &length, sizeof(int));
    char *buf = (char*) malloc(length);
    string file_name[2];
    int trace_kind = 0;
    file_name[0] = temp_dir + string("trace.log");
    file_name[1] = temp_dir + string("dangertrace.log");
    for (int i = 0; i < 2; i ++)
    {
        file_fd[i] = open(file_name[i].c_str(), 
                          O_WRONLY | O_TRUNC | O_CREAT, PERM_R_W);
        if (file_fd[i] == -1)
        {
            LOG(Logger::ERROR, "Cannot open file " << file_name[i] <<
                               ": " << strerror(errno));
            throw "local";
        }
    }
    do
    {
        readFromSocket(fd, &trace_kind, sizeof(int));
        if ((trace_kind < 1) || trace_kind > 2)
        {
            break;
        }
        readFromSocket(fd, &length, sizeof(int));
        readFromSocket(fd, buf, length);
        if (write(file_fd[trace_kind - 1], buf, length) < 1)
        {
            LOG(Logger::ERROR, "Cannot write to file " << 
                               file_name[trace_kind - 1] << 
                               ": " << strerror(errno));
            throw "local";
        }
    }
    while (true);
    free(buf);
}

bool RemotePluginExecutor::checkFlag(const char *flg_name)
{
    for (int i = 0; i < argsnum; i ++)
    {
        if(strstr(args[i], flg_name) == args[i])
        {
            return true;
        }
    }
    return false;
}

RemotePluginExecutor::RemotePluginExecutor(vector<string> &_args, 
                                           int _remote_fd, vector<char> &to_send,
                                           string _result_dir)
{
    remote_fd = _remote_fd;
    result_dir = _result_dir;
    argsnum = _args.size();
    args = (char **)calloc (argsnum, sizeof(char *));
    files_to_send = to_send;
    for (int i = 0; i < argsnum; i ++)
    {
        args[i] = strdup(_args[i].c_str());
    }
}

int RemotePluginExecutor::run(int thread_index)
{
    int res, size;
    try
    {
        char util_c;
        char *file_name;
        int i, arg_length, file_length;
        writeToSocket(remote_fd, &argsnum, sizeof(int));
        for (i = 0; i < argsnum; i ++)
        {
            arg_length = strlen(args[i]);
            writeToSocket(remote_fd, &arg_length, sizeof(int));
            writeToSocket(remote_fd, args[i], arg_length);
            util_c = files_to_send[i] ? '1' : '\0';
            writeToSocket(remote_fd, &util_c, 1);
            if (util_c)
            {
                char *eq_sign = strchr(args[i], '=');
                if (eq_sign != NULL)
                {
                    eq_sign ++;
                    file_name = eq_sign;
                }
                else
                {
                    file_name = args[i];
                }
                string s_file_name = file_name;
                FileBuffer f(s_file_name);
                size = f.getSize();
                writeToSocket(remote_fd, &size, sizeof(int));
                writeToSocket(remote_fd, f.buf, size);
            }
        }
        string temp_dir = ExecutionManager::getTempDir();
        if (checkFlag("--check-prediction=yes"))
        {
            writeFileToSocket(remote_fd, temp_dir + string("prediction.log"));
        }
        if (checkFlag("--replace=yes") || checkFlag("--replace=replace_data"))
        {
            writeFileToSocket(remote_fd, temp_dir + string("replace_data"));
        }
        if (checkFlag("--check-argv="))
        {
            writeFileToSocket(remote_fd, temp_dir + string("arg_lengths"));
        }
      //  readFromSocket(remote_fd, &res, sizeof(int));

        if (checkFlag("--tool=tracegrind"))
        { 
            readTraceOnTheRun(remote_fd, temp_dir);
            readFromSocket(remote_fd, &res, sizeof(int));
            if (res == 1)
            {
                LOG(Logger::ERROR, "Plugin-agent ended abnormally");
                return 1;
            }
            readFileFromSocket(remote_fd, temp_dir + string("offsets.log"));
            if (checkFlag("--dump-prediction=yes"))
            {
               readFileFromSocket(remote_fd, temp_dir + string("actual.log"));
            }
            if (checkFlag("--dump-file=calldump.log"))
            {
               readFileFromSocket(remote_fd, 
                                      result_dir + string("calldump.log"));
            }
            if (checkFlag("--sockets=yes") || checkFlag("--datagrams=yes"))
            {
               readFileFromSocket(remote_fd, 
                                      temp_dir + string("replace_data"));
            }
            if (checkFlag("--check-argv="))
            {
               readFileFromSocket(remote_fd, temp_dir + string("argv.log"));
            }
        }
        else
        {
            readFromSocket(remote_fd, &res, sizeof(int));
            if (!checkFlag("--no-coverage=yes"))
            {
                readFileFromSocket(remote_fd, 
                                       temp_dir + string("basic_blocks.log"));
            }
            readFileFromSocket(remote_fd, temp_dir + string("execution.log"));
        }
    }
    catch(const char *msg)
    {
        if (!strcmp(msg, "net"))
        {
            LOG(Logger::NETWORK_LOG, "Connection with plugin-agent is down");
        }
        return 1;
    }
    return res;
}
