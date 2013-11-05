
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

#include "alloc.h"
#include "list.h"

size_t g_alloc_total;
TrackAlloc *g_alloc_list;

void ResetAllocs()
{
  g_alloc_total = 0;
  TrackAlloc *t = g_alloc_list;
  while (t != NULL) {
    t->alloc_total = 0;
    t = t->next;
  }
}

inline void PrintBytes(size_t bytes)
{
  if (bytes < 1024)
    logout << bytes << " B";
  else if (bytes < 1048576)
    logout << (bytes >> 10) << " kB";
  else
    logout << (bytes >> 20) << " mB";
}

void PrintAllocs()
{
  logout << "Allocations: ";
  PrintBytes(g_alloc_total);
  logout << endl;

  size_t net_total = 0;

  TrackAlloc *t = g_alloc_list;
  while (t != NULL) {
    if (t->alloc_total != 0) {
      net_total += t->alloc_total;
      logout << "  " << t->name << ": ";
      PrintBytes(t->alloc_total);
      logout << endl;
    }
    t = t->next;
  }

  logout << "  Net: ";
  PrintBytes(net_total);
  logout << endl << endl;
  logout << flush;
}

// function to ensure the list of allocators is properly initialized
// by the time we get around to traversing it (possibly during static
// initialization).
void InitializeAllocList()
{
  static bool initialized_alloc = false;
  if (!initialized_alloc) {
    initialized_alloc = true;
    g_alloc_list = NULL;
  }
}

// explicitly do *NOT* initialize alloc_total here. this is garbage anyways
// since the value may have already been increased by allocations performed
// before this structure was initialized.
TrackAlloc::TrackAlloc(const char *_name)
  : name(_name), next(NULL)
{
  InitializeAllocList();

  // insert this allocator in its sorted order by the allocator name.
  TrackAlloc **pprev = &g_alloc_list;
  while (*pprev && strcmp(name, (*pprev)->name) > 0)
    pprev = &(*pprev)->next;

  next = *pprev;
  *pprev = this;
}

TrackAlloc& LookupAlloc(const char *name)
{
  InitializeAllocList();

  TrackAlloc *alloc = g_alloc_list;
  while (alloc) {
    int cmp = strcmp(name, alloc->name);
    if (cmp == 0)
      return *alloc;
    alloc = alloc->next;
  }

  // make a new allocator. its constructor will thread it onto g_alloc_list.
  alloc = new TrackAlloc(name);
  return *alloc;
}

TrackAlloc g_alloc_Vector("Vector");
TrackAlloc g_alloc_HashCache("HashCache");
TrackAlloc g_alloc_HashTable("HashTable");
