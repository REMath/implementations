/*----------------------------------------------------------------------------------------*/
/*------------------------------------- AVALANCHE ----------------------------------------*/
/*------ Driver. Coordinates other processes, traverses conditional jumps tree.  ---------*/
/*-------------------------------------- Logger.h ----------------------------------------*/
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

#ifndef __LOGGER__H__
#define __LOGGER__H__

#include <cstddef>
#include <sstream>
#include <string>


class Logger
{
private:

	bool verbose;
	bool debug;
	bool programOutput;
	bool networkLog;

public:

	enum Level 
	{
		JOURNAL, 
		VERBOSE, 
		PROGRAM_OUTPUT,
		NETWORK_LOG,
		ERROR,
		REPORT, // printing final report
		DEBUG
	};

	Logger (): verbose (false), debug (false), programOutput (false), 
		networkLog (false) {}

	void setVerbose ();
	void setDebug ();
	void setProgramOutput ();
	void setNetworkLog ();
	
	static Logger * getLogger ();

	void write (Level level, const std::string &msg, const char *file, 
		std::size_t line) const;
};

// Printing log message

#define LOG(level, msg) \
	do { \
		std :: ostringstream log_buf; \
		log_buf << msg; \
		logger -> write (level, log_buf.str (), __FILE__, __LINE__); \
	} while (0)

// Printing log message with time

#define LOG_TIME(level, msg) \
	do { \
		time_t tt = time (NULL); \
		string t = string (ctime (& tt)); \
		std :: ostringstream log_buf; \
		log_buf << msg << " \033[2m" << t.substr (0, t.size() - 1) << "\033[0m"; \
		logger -> write (level, log_buf.str (), __FILE__, __LINE__); \
	} while (0)

#endif //__LOGGER__H__

