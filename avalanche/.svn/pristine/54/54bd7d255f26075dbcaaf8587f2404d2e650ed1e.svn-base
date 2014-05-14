/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*------------------------------------ TmpFile.cpp ---------------------------------------*/
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

#include <stdlib.h>

#include <unistd.h>
#include <cerrno>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <set>

#include "Logger.h"
#include "TmpFile.h"
#include "ExecutionManager.h"

using namespace std;

static Logger *logger = Logger::getLogger();

unsigned int TmpFile::tmpnum = 0;

TmpFile::TmpFile(): is_good(true)
{
    char s[64];
    sprintf(s, "tmpfile_%u", tmpnum++);
    filename = strdup((ExecutionManager::getTempDir() + string(s)).c_str());
    FILE *fp = fopen(filename, "wt");
    
    if (!fp) 
    {
        is_good = false;
        LOG (Logger :: ERROR, "Cannot open file " << filename << ":" << strerror(errno));
    }
    else
    {
        fclose(fp);
    }
}

TmpFile::~TmpFile()
{
    if (::unlink(filename) == -1)
    {
        LOG (Logger :: ERROR, "Cannot delete file " << 
                              filename <<":"<< strerror(errno));
    }

    free(filename);
}

void TmpFile::print() const
{
    if (is_good != true) return;

    ifstream in_file(filename);

    while (in_file.eof() != true) {
        char buf[65536];

        in_file.getline(buf, 65536);
        LOG (Logger :: DEBUG, buf);
    }
    in_file.close();
}

