/*---------------------------------------------------------------------------*/
/*------------------------------ AVALANCHE ----------------------------------*/
/*- Driver. Coordinates other processes, traverses conditional jumps tree.  -*/
/*------------------------------ Executor.h ---------------------------------*/
/*---------------------------------------------------------------------------*/

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

#ifndef __EXECUTOR__H__
#define __EXECUTOR__H__

#include <cstdlib>

enum Kind
{
    TG,
    CV,
    MC,
    HG,
    UNID
};

class Executor
{
public:
    Executor() : args(NULL), argsnum(0) {}
    virtual ~Executor()
    {
        for (int i = 0; i < argsnum; i ++)
        {
            free(args[i]);
        }
        free(args);
    }
    virtual int run(int thread_index = 0) = 0;

protected:
    char **args;
    unsigned int argsnum;
};

#endif //__EXECUTOR__H__

