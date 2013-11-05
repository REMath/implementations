/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*---------------------------------- SocketBuffer.h --------------------------------------*/
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

#ifndef __SOCKET_BUFFER__H__
#define __SOCKET_BUFFER__H__

#include "FileBuffer.h"

class SocketBuffer : public FileBuffer
{
public:

  int num;

  SocketBuffer(int _num, int _size);

  SocketBuffer(const SocketBuffer& other);

  virtual FileBuffer* forkInput(FileBuffer *stp_file, 
                                std::vector<FileOffsetSet> &used_offsets);

  virtual int dumpFile(std::string file_name);
  
  virtual int applySTPSolution(char* buf, 
                               std::vector<FileOffsetSet> &used_offsets);

  ~SocketBuffer();

};

#endif
