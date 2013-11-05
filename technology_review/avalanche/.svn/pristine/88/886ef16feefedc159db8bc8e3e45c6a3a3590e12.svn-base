/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*------------------------------------- Input.cpp ----------------------------------------*/
/*----------------------------------------------------------------------------------------*/

/*
   Copyright (C) 2010 Ildar Isaev
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
#include <string.h>
#include <fcntl.h>
#include <cerrno>

#include "Input.h"
#include "FileBuffer.h"
#include "ExecutionManager.h"
#include "Logger.h"

using namespace std;

static Logger* logger = Logger::getLogger();

Input::Input()
{
    startdepth = 0;
    prediction = NULL;
    prediction_size = 0;
    parent = NULL;
}

Input::~Input()
{
    if (prediction != NULL)
    {
        delete []prediction;
    }
    for (int i = 0; i < files.size(); i ++)
    {
        delete (files.at(i));
    }
}

int Input::dumpExploit(string file_name, bool predict, string name_modifier)
{
    std::string res_name = file_name + name_modifier;
    int fd = open(res_name.c_str(), O_WRONLY | O_TRUNC | O_CREAT,
                  S_IRUSR | S_IROTH | S_IRGRP | S_IWUSR | S_IWOTH | S_IWGRP);
    if (fd == -1)
    {
        LOG(Logger::ERROR, "Cannot open file " << res_name <<
                           " :" << strerror(errno));
        return -1;
    }
    int size = files.size();
    if (write(fd, &size, sizeof(int)) < 1)
    {
        LOG(Logger::ERROR, "Cannot write to file " << res_name <<
                           " :" << strerror(errno));
        close(fd);
        return -1;
    }
    for (int i = 0; i < files.size(); i++)
    {
        int error;
        size = files.at(i)->getSize();
        error = write(fd, &size, sizeof(int));
        if (error > 0)
        {
            error = write(fd, files.at(i)->buf, size);
        }
        if (error < 1)
        {
            LOG(Logger::ERROR, "Cannot write to file " << res_name <<
                           " :" << strerror(errno));
            close(fd);
            return -1;
        }
    }
    close(fd);
    if (predict && (prediction != NULL))
    {
        string prediction_file = ExecutionManager::getTempDir() + 
                                                      string("prediction.log");
        fd = open(prediction_file.c_str(), O_WRONLY | O_TRUNC | O_CREAT, 
                  S_IRUSR | S_IROTH | S_IRGRP | S_IWUSR | S_IWOTH | S_IWGRP);
        if (fd == -1)
        {
            LOG(Logger::ERROR, "Cannot open file " << prediction_file <<
                           " :" << strerror(errno));
            return -1;
        }
        if (write(fd, prediction, prediction_size * sizeof(bool)) < 1)
        {
            LOG(Logger::ERROR, "Cannot write to file " << prediction_file <<
                           " :" << strerror(errno));
            close(fd);
            return -1;
        }
        close(fd);
    }
    return 0; 
}

int Input::dumpFiles(string name_modifier)
{
    for (int i = 0; i < files.size(); i++)
    {
        string res_name = files.at(i)->getName() + name_modifier;
        if (files.at(i)->dumpFile(res_name) < 0)
        {
            return -1;
        }
    }
    if (prediction != NULL)
    {
        string prediction_file = ExecutionManager::getTempDir() +
                                                         string("prediction.log");
        int fd = open(prediction_file.c_str(), O_WRONLY | O_TRUNC | O_CREAT,
                                    S_IRUSR | S_IROTH | S_IRGRP | S_IWUSR | S_IWOTH | S_IWGRP);
        write(fd, prediction, prediction_size * sizeof(bool));
        if (fd == -1)
        {
            LOG(Logger::ERROR, "Cannot open file " << prediction_file <<
                           " :" << strerror(errno));
            return -1;
        }
        if (write(fd, prediction, prediction_size * sizeof(bool)) < 1)
        {
            LOG(Logger::ERROR, "Cannot write to file " << prediction_file <<
                           " :" << strerror(errno));
            close(fd);
            return -1;
        }
        close(fd);
    }
    return 0;
}
