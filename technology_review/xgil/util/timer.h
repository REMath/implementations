
// Sixgill: Static assertion checker for C/C++ programs.
// Copyright (C) 2009-2010  Stanford University
// Author: Brian Hackett
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

// fairly fine granularity profiling information.
// for more detailed data use gprof.

#include "assert.h"
#include <sys/time.h>

NAMESPACE_XGILL_BEGIN

// print the specified elapsed time, in microseconds, to stdout.
void PrintTime(uint64_t usec);

// print all timing info to stdout.
void PrintTimers();

// aggregate data about all the times a particular timer is used.
struct BaseTimer
{
  // make a new base timer with a globally unique name.
  BaseTimer(const char *name);

  // add a new use of this timer.
  void AddUse(uint64_t usec)
  {
    m_count++;
    m_usec += usec;
  }

  // name of this timer.
  const char *m_name;

  // number of times this timer has been invoked.
  uint64_t m_count;

  // total number of microseconds used for this timer.
  uint64_t m_usec;

  // next timer in global list.
  BaseTimer *m_next;
};

// head of the global list of timers.
extern BaseTimer *g_timer_list;

// get the time of day in microseconds.
static inline uint64_t GetCurrentTime()
{
  timeval current;
  gettimeofday(&current, NULL);
  return current.tv_sec * (uint64_t) 1000000 + current.tv_usec;
}

// individual timer structure. constructing this starts the timer, destructing
// it ends the timer and adds a use to the aggregate base timer.
class Timer
{
 public:
  Timer(BaseTimer *base = NULL)
    : m_base(base), m_start(GetCurrentTime())
  {}

  // time in microseconds which has elapsed since this timer started.
  uint64_t Elapsed()
  {
    uint64_t current = GetCurrentTime();
    Assert(current >= m_start);
    return current - m_start;
  }

  ~Timer()
  {
    uint64_t elapsed = Elapsed();
    if (m_base)
      m_base->AddUse(elapsed);
  }

 private:
  // optional base timer to use. if not specified, the timer does nothing
  // except answer Elapsed() queries.
  BaseTimer *m_base;

  // time when this timer was started.
  uint64_t m_start;
};

// alarm style timer for soft timeouts.
class TimerAlarm
{
 public:
  // make an alarm which will expire after the specified number of seconds.
  TimerAlarm(uint64_t seconds)
    : m_start(GetCurrentTime())
  {
    m_end = m_start + (seconds * 1000000);
  }

  // whether this alarm has expired.
  bool Expired()
  {
    return GetCurrentTime() >= m_end;
  }

  // time in microseconds which has elapsed since this alarm started.
  uint64_t Elapsed()
  {
    uint64_t current = GetCurrentTime();
    Assert(current >= m_start);
    return current - m_start;
  }

 private:
  // time when this alarm started.
  uint64_t m_start;

  // time when this alarm will expire.
  uint64_t m_end;

  // active alarm for below.
  static TimerAlarm *g_active_alarm;

 public:
  // stat/clear/check a global active alarm. various components of the system
  // check these to see if they should finish prematurely.

  static void StartActive(uint64_t seconds)
  {
    Assert(!g_active_alarm);
    g_active_alarm = new TimerAlarm(seconds);
  }

  static void ClearActive()
  {
    if (g_active_alarm) {
      delete g_active_alarm;
      g_active_alarm = NULL;
    }
  }

  static bool ActiveExpired()
  {
    if (g_active_alarm)
      return g_active_alarm->Expired();
    return false;
  }

  static uint64_t ActiveElapsed()
  {
    Assert(g_active_alarm);
    return g_active_alarm->Elapsed();
  }
};

NAMESPACE_XGILL_END
