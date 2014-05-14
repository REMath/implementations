/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*----------------------------------- FileBuffer.h ---------------------------------------*/
/*----------------------------------------------------------------------------------------*/

/*
   Copyright (C) 2009-2011 Ildar Isaev
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

#ifndef __FILE_BUFFER__H__
#define __FILE_BUFFER__H__

#include <cstddef>
#include <string>
#include <sys/types.h>
#include <set>
#include <vector>

struct FileOffsetSet
{
  std::string file_name;
  std::set<unsigned long> offset_set;
};

class FileBuffer
{
public:

    char* buf;
    int sd;

    friend bool operator == (const FileBuffer& arg1, const FileBuffer& arg2);

    FileBuffer(std::string file_name);

    FileBuffer(const FileBuffer& other);
    FileBuffer(char* buf);

    virtual FileBuffer* forkInput(FileBuffer *stp_file, 
                                  std::vector<FileOffsetSet> &used_offsets);

    virtual int dumpFile(std::string file_name = "");

    int cutQueryAndDump(std::string file_name, bool do_invert = false);

    virtual int applySTPSolution(char* buf, 
                                 std::vector<FileOffsetSet> &used_offsets);
    
    std::string getName() const
    { return name; }

    int getSize() const
    { return size; }

    void setSize(int _size)
    { size = _size; }

    ~FileBuffer();

protected:
    int size;
    std::string name;
  
    FileBuffer() {}

};

#define PERM_R_W   S_IRUSR | S_IROTH | S_IRGRP | \
                   S_IWUSR | S_IWOTH | S_IWGRP

#endif
