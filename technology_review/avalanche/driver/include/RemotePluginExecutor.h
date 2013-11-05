/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*-------------------------------- RemotePluginExecutor.h --------------------------------*/
/*----------------------------------------------------------------------------------------*/

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

#ifndef __REMOTE_PLUGIN_EXECUTOR__H__
#define __REMOTE_PLUGIN_EXECUTOR__H__

#include "Executor.h"
#include <string>
#include <vector>

class RemotePluginExecutor : public Executor
{
public:
    RemotePluginExecutor(std::vector<std::string> &_args, int fd, std::vector<char> &to_send, std::string _result_dir);
    bool checkFlag(const char *flg_name);
    ~RemotePluginExecutor() {}
    int run(int thread_index = 0);

private:
    int remote_fd;
    std::vector<char> files_to_send;
    std::string result_dir;
};


#endif //__REMOTE_PLUGIN_EXECUTOR__H__

