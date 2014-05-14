
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

#include "timer.h"

NAMESPACE_XGILL_BEGIN

// BaseTimer() initializes this variable the first time it is called,
// to avoid issues with timing functions called during static initialization.
BaseTimer *g_timer_list;

BaseTimer::BaseTimer(const char *name)
  : m_name(name), m_count(0), m_usec(0), m_next(NULL)
{
  // make sure the global timer list is initialized, per above.
  static bool init_timer_list = false;
  if (!init_timer_list) {
    g_timer_list = NULL;
    init_timer_list = true;
  }

  m_next = g_timer_list;
  g_timer_list = this;
}

#define USEC_PER_SECOND  1000000

void PrintTime(uint64_t usec)
{
  uint64_t minutes = usec / USEC_PER_SECOND / 60;

  logout << minutes << ":";
  usec = usec % (USEC_PER_SECOND * 60);

  uint64_t seconds = usec / USEC_PER_SECOND;
  if (seconds < 10)
    logout << "0";
  logout << seconds;
  usec = usec % USEC_PER_SECOND;

  logout << ".";

  uint64_t hundredths = usec / (USEC_PER_SECOND / 100);
  if (hundredths < 10)
    logout << "0";
  logout << hundredths;
}

void PrintTimers()
{
  // make sure there is at least one base timer, and that g_timer_list
  // is guaranteed to be initialized when we start traversing it.
  static BaseTimer empty_timer("");

  logout << "Timers:" << endl;

  BaseTimer *timer = g_timer_list;
  while (timer) {
    if (timer->m_count) {
      logout << "  " << timer->m_name << " (" << timer->m_count << "): ";
      PrintTime(timer->m_usec);
      logout << endl;
    }
    timer = timer->m_next;
  }
}

TimerAlarm* TimerAlarm::g_active_alarm = NULL;

NAMESPACE_XGILL_END
