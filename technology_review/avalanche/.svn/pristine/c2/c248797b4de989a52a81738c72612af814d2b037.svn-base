/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*------------------------------------ Logger.cpp ----------------------------------------*/
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

#include <string>
#include <iostream>

#include "Logger.h"
#include "stdio.h"

using namespace std;


static Logger *logger = NULL;

Logger * Logger :: getLogger ()
{
  if (logger == NULL) 
    logger = new Logger;

  return logger;
}

void Logger :: setVerbose ()
{ 
  verbose = true; 
}

void Logger :: setDebug ()
{
  debug = true;
}

void Logger :: setProgramOutput ()
{
  programOutput = true;
}

void Logger :: setNetworkLog ()
{
  networkLog = true;
}
  
void Logger::write(Level level, const string & msg, const char * file, size_t line) const
{
  string message = msg;

  // Clear colors

  if (!isatty (fileno (stdout))) // if not a terminal
  {
    int i = 0, j;

    while (1)
    {
      if ((i = message.find ("\033", i)) != -1)
      {
        for (j = i; message [j] != 'm'; j++);
        message.replace (i, j - i + 1, "");
      }
      else break;
    }
  }

  switch (level) 
  {
  // Always

  case ERROR:
    cout << "Error: " << message << endl;
    break;

  case REPORT:
  case JOURNAL:
    cout << message << endl; 
    break;

  // Optional

  case DEBUG:
    if (debug)
    {
      cout << message << endl;
    }
    break;

  case VERBOSE:
    if (verbose || debug) 
    {
      cout << message << endl;
    }
    break;

  case PROGRAM_OUTPUT:
    if (programOutput) 
    {
      cout << "Program output: " << message << endl;
    }
    break;

  case NETWORK_LOG:
    if (networkLog) 
    {
      cout << "Network log: " << message << endl;
    }
    break;
  
  default:
    cout << "Unknown logging level, log message: " << message << endl;
  }
}
