/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*---------------------------------- PluginExecutor.h ------------------------------------*/
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

#ifndef __PLUGIN_EXECUTOR__H__
#define __PLUGIN_EXECUTOR__H__

#include "LocalExecutor.h"

#include <vector>
#include <string>

class OptionConfig;

class PluginExecutor : public LocalExecutor
{
public:
    PluginExecutor(bool debug_full_enable,
                   bool trace_children,
                   const std::string &valgrind_binary,
                   const std::vector<std::string> &cmd,
                   const std::vector<std::string> &tg_args);

    int run(int thread_index = 0);
    ~PluginExecutor();

private:
    bool debug_full;
    bool trace_children;
};


#endif //__PLUGIN_EXECUTOR__H__

