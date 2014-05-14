/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*---------------------------------- SocketBuffer.cpp ------------------------------------*/
/*----------------------------------------------------------------------------------------*/

/*
   Copyright (C) 2009 Ildar Isaev
      iisaev@ispras.ru

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
#include <sys/stat.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <cerrno>

#include "SocketBuffer.h"
#include "Logger.h"

using namespace std;

static Logger *logger = Logger::getLogger();

SocketBuffer::SocketBuffer(int _num, int _size) : num(_num)
{
    size = _size;
    name = string("");
    if ((buf = (char*) malloc (size)) == NULL)
    {
        LOG(Logger::ERROR, strerror(errno));
        throw "malloc";
    }
    memset(buf, 0, size);
}

SocketBuffer::SocketBuffer(const SocketBuffer& other)
{
    name = string("");
    num = other.num;
    size = other.getSize();
    if ((buf = (char*) malloc (size)) == NULL)
    {
        LOG(Logger::ERROR, strerror(errno));
        throw "malloc";
    }
    strncpy(buf, other.buf, size);
    buf[size] = '\0';
}

FileBuffer* SocketBuffer::forkInput(FileBuffer *stp_file,
                                    vector<FileOffsetSet> &used_offsets)
{
    if (stp_file->getSize() > strlen("Valid"))
    {
         if (!strncmp(stp_file->buf, "Valid", strlen("Valid")))
         {
             return NULL;
         }
    }
    SocketBuffer* res;
    try
    {
        res = new SocketBuffer(*this);
    }
    catch (const char *)
    {
        return NULL;
    }
    catch (std::bad_alloc)
    {
        LOG(Logger::ERROR, strerror(errno));
        return NULL;
    }
    if (res->applySTPSolution(stp_file->buf, used_offsets) < 0)
    {
        return NULL;
    }
    return res;
}

int SocketBuffer::dumpFile(string file_name)
{    
}
    
int SocketBuffer::applySTPSolution(char* buf,
                                   vector<FileOffsetSet> &used_offsets)
{
    char* pointer = buf;
    char* byte_value;
    while ((byte_value = strstr(pointer, "socket_")) != NULL)
    {
        char* brack = strchr(byte_value, '[');
        if (brack == NULL)
        {
            return -1;
        }
        *brack = '\0';
        int number = atoi(byte_value + 7);
        if (num == number)
        {
            char* pos_begin = brack + 5;
            char* pos_end;
            long index = strtol(pos_begin, &pos_end, 16);
            if ((index < 0) || (index > size))
            {
                return -1;
            }
            char* value_begin = pos_end + 9;
            long value = strtol(value_begin, &pointer, 16);
            this->buf[index] = value;
        }
        else
        {
            pointer = brack + 5;
        }
        *brack = '[';
    }
    return 0;
}

SocketBuffer::~SocketBuffer()
{
    free(buf);
}

