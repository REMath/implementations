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

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/resource.h>

int _global_debug_leveli = 0;

int _global_check_level = 0;

void fatal(const char * fun, const char * file, int lineno, const char * fmt, ...) {
  va_list ap;
  fprintf(stderr, "***");
  if (fun)
    fprintf(stderr, " in %s", fun);
  if (file)
    fprintf(stderr, " at %s", file);
  if (lineno)
    fprintf(stderr, ":%d", lineno);
  fprintf(stderr, " ");
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fflush(stderr);
  exit(1);
}

void warning(const char * fun, const char * file, int lineno, const char * fmt, ...) {
  va_list ap;
  fprintf(stderr, "***");
  if (fun)
    fprintf(stderr, " in %s", fun);
  if (file)
    fprintf(stderr, " at %s", file);
  if (lineno)
    fprintf(stderr, ":%d", lineno);
  fprintf(stderr, " ");

  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fflush(stderr);
}

double get_cpu_time(void) {
  double res;
  struct rusage usage;
  getrusage(RUSAGE_SELF, &usage);
  res = usage.ru_utime.tv_usec + usage.ru_stime.tv_usec;
  res *= 1e-6;
  res += usage.ru_utime.tv_sec + usage.ru_stime.tv_sec;
  return res;
}
