
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

// command line and file configuration for the various xgill apps

#include "vector.h"

NAMESPACE_XGILL_BEGIN

enum ConfigOptionKind {
  CK_Invalid = 0,
  CK_Flag = 1,
  CK_Int = 2,
  CK_UInt = 3,
  CK_String = 4
};

class ConfigOption
{
 public:
  // creates and registers a new configuration option.
  // this constructor should be used during static initialization.
  ConfigOption(ConfigOptionKind _kind,
               const char *name, const char *default_value,
               const char *description);

  // enable this configuration option to be used at the command line.
  // this must be called before the configuration is parsed.
  void Enable();

  // get the kind of this option.
  ConfigOptionKind Kind() const { return m_kind; }

  // get the name of this option.
  const char* Name() const { return m_name; }

  // print information on this option to cout.
  void Print();

  // sets the value of this option. this is called by Config::Parse
  // but can also be called explicitly by clients. returns false if
  // the value is malformed (i.e. non-integer for an integer option).
  bool SetValue(const char *value);

  // whether this option was specified at the command line or by
  // a call to SetValue().
  bool IsSpecified() const { return m_specified; }

  // accessors for the different kinds of options. the accessor used
  // must match the kind field. if SetValue() was not called then
  // these will return the default value.

  long IntValue() const
  {
    Assert(m_kind == CK_Int);
    return m_use_int;
  }

  unsigned long UIntValue() const
  {
    Assert(m_kind == CK_UInt);
    Assert(m_use_int >= 0);
    return (unsigned long) m_use_int;
  }

  const char* StringValue() const
  {
    Assert(m_kind == CK_String);
    return m_use_string;
  }

 private:

  ConfigOptionKind m_kind;
  const char *m_name;
  const char *m_default_value;
  const char *m_description;

  // whether SetValue() was called with a new value.
  bool m_specified;

  // the value of this option as an int/string. uses the default
  // if SetValue() was never called.
  long m_use_int;
  const char *m_use_string;
};

namespace Config
{
  // parse the command line arguments, going into any configuration
  // files specified. any options that do not have a switch will
  // be put into unspecified, in the order in which they appeared in argv.
  // returns true on success, false and prints error otherwise.
  bool Parse(int argc, const char **argv,
             Vector<const char*> *unspecified);

  // prints the specified usage message, along with descriptions of
  // all the configuration options.
  void PrintUsage(const char *usage);
}

NAMESPACE_XGILL_END
