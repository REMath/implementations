// *********************************************************************
// Copyright 2000-2004, Princeton University.  All rights reserved.
// By using this software the USER indicates that he or she has read,
// understood and will comply with the following:
//
// --- Princeton University hereby grants USER nonexclusive permission
// to use, copy and/or modify this software for internal, noncommercial,
// research purposes only. Any distribution, including commercial sale
// or license, of this software, copies of the software, its associated
// documentation and/or modifications of either is strictly prohibited
// without the prior consent of Princeton University.  Title to copyright
// to this software and its associated documentation shall at all times
// remain with Princeton University.  Appropriate copyright notice shall
// be placed on all software copies, and a complete copy of this notice
// shall be included in all copies of the associated documentation.
// No right is  granted to use in advertising, publicity or otherwise
// any trademark,  service mark, or the name of Princeton University.
//
//
// --- This software and any associated documentation is provided "as is"
//
// PRINCETON UNIVERSITY MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS
// OR IMPLIED, INCLUDING THOSE OF MERCHANTABILITY OR FITNESS FOR A
// PARTICULAR PURPOSE, OR THAT  USE OF THE SOFTWARE, MODIFICATIONS, OR
// ASSOCIATED DOCUMENTATION WILL NOT INFRINGE ANY PATENTS, COPYRIGHTS,
// TRADEMARKS OR OTHER INTELLECTUAL PROPERTY RIGHTS OF A THIRD PARTY.
//
// Princeton University shall not be liable under any circumstances for
// any direct, indirect, special, incidental, or consequential damages
// with respect to any claim by USER or any third party on account of
// or arising from the use, or inability to use, this software or its
// associated documentation, even if Princeton University has been advised
// of the possibility of those damages.
// *********************************************************************

#ifndef __ZCHAFF_INCLUDE__
#define __ZCHAFF_INCLUDE__

#define WORD_SIZE 4
// #define WORD_SIZE 8

extern int _global_debug_level;
extern int _global_check_level;

#ifndef __FUNCTION__
# define __FUNCTION__ ((char*)0)
#endif

#ifndef __FILE__
# define __FILE__ 0
#endif

#ifndef __LINE__
# define __LINE__ 0
#endif

#define _POSITION_  __FUNCTION__, __FILE__, __LINE__

#if WORD_SIZE == 4
#define WORD_WIDTH         32
typedef unsigned        uint32;
typedef int             int32;
typedef long long       long64;
#elif WORD_SIZE == 8
#define WORD_WIDTH         64
typedef unsigned int    uint32;
typedef int             int32;
typedef long            long64;
#endif

void fatal(const char * fun, const char * file, int lineno, const char * fmt, ...);
void warning(const char * fun, const char * file, int lineno, const char * fmt, ...);
double get_cpu_time(void);

#endif
