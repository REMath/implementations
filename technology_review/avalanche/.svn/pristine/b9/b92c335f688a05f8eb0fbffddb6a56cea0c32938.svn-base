/*---------------------------------------------------------------------------*/
/*------------------------------- AVALANCHE ---------------------------------*/
/*- Driver. Coordinates other processes, traverses conditional jumps tree.  -*/
/*-------------------------- ExecutionLogBuffer.h ---------------------------*/
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

#ifndef __EXECUTION_LOG_BUFFER__H__
#define __EXECUTION_LOG_BUFFER__H__

#include "FileBuffer.h"
#include "Error.h"
#include <string>
#include <vector>

class ExecutionLogBuffer : public FileBuffer
{
public:
    ExecutionLogBuffer(std::string _file_name);
    ~ExecutionLogBuffer() {}
 
    Error* getCrashError();   
    std::vector<Error*> getErrors(std::string plugin_name);
};

#endif // __EXECUTION_LOG_BUFFER__H__
