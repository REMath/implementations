// $Id: OptionParser.h 80 2009-10-30 18:55:50Z iisaev $
/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*---------------------------------- OptionParser.h --------------------------------------*/
/*----------------------------------------------------------------------------------------*/

/*
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

#ifndef __OPTION_PARSER__H__
#define __OPTION_PARSER__H__

#include <vector>
#include <string>

class OptionConfig;


class OptionParser
{
public:
    OptionParser(int argc, char *argv[]);

    OptionConfig *run() const;
    void reportDummyOptions(OptionConfig* config) const;
    bool checkSupportedPlugins(std::string plugin_name) const;

protected:
    void setProgName(const std::string &path);

private:
    std::string progName;
    std::vector<std::string> args;
};


#endif //__OPTION_PARSER__H__

