
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

#include "buffer.h"
#include "config.h"
#include "assert.h"

NAMESPACE_XGILL_BEGIN

static bool command_line_parsed = false;

// configuration options which are enabled.
static Vector<ConfigOption*> options;

/////////////////////////////////////////////////////////////////////
// ConfigOption
/////////////////////////////////////////////////////////////////////

ConfigOption::ConfigOption(ConfigOptionKind kind,
                           const char *name, const char *default_value,
                           const char *description)
  : m_kind(kind), m_name(name),
    m_default_value(default_value),
    m_description(description),
    m_specified(false), m_use_int(0), m_use_string(NULL)
{
  Assert(!command_line_parsed);
  Assert(name);
  Assert(description);

  Assert(strlen(name) > 0);

  switch (kind) {
  case CK_Flag:
    Try(default_value == NULL);
    break;
  case CK_Int:
    Try(default_value != NULL);
    Try(StringToInt(default_value, &m_use_int));
    break;
  case CK_UInt:
    Try(default_value != NULL);
    Try(StringToInt(default_value, &m_use_int));
    Assert(m_use_int >= 0);
    break;
  case CK_String:
    Try(default_value != NULL);
    m_use_string = default_value;
    break;
  default:
    Assert(false);
  }
}

void ConfigOption::Enable()
{
  Assert(!command_line_parsed);

  // watch for duplicate names.
  for (size_t ind = 0; ind < options.Size(); ind++) {
    if (!strcasecmp(options[ind]->m_name, m_name)) {
      printf("Duplicate configuration option: %s\n", m_name);
      Assert(false);
    }
  }

  options.PushBack(this);
}

void ConfigOption::Print()
{
  cout << "-" << m_name;
  if (m_default_value != NULL)
    cout << "=" << m_default_value;
  cout << endl;
  cout << "    " << m_description << endl;
}

bool ConfigOption::SetValue(const char *value)
{
  Assert(value);

  Assert(!m_specified);
  m_specified = true;

  switch (m_kind) {
  case CK_Flag:
    if (*value != 0) {
      cout << "ERROR: Option " << m_name
           << " cannot be used with a value." << endl;
      return false;
    }
    return true;
  case CK_Int:
    if (!StringToInt(value, &m_use_int)) {
      cout << "ERROR: Option " << m_name
           << " must have an integer value." << endl;
      return false;
    }
    return true;
  case CK_UInt:
    if (!StringToInt(value, &m_use_int) || m_use_int < 0) {
      cout << "ERROR: Option " << m_name
           << " must have a non-negative integer value." << endl;
      return false;
    }
    return true;
  case CK_String:
    if (*value == 0) {
      cout << "ERROR: Option " << m_name
           << " must be used with a non-empty value." << endl;
      return false;
    }
    m_use_string = value;
    return true;
  default:
    Assert(false);
    return false;
  }
}

/////////////////////////////////////////////////////////////////////
// Config
/////////////////////////////////////////////////////////////////////

bool Config::Parse(int argc, const char **argv,
                   Vector<const char*> *unspecified)
{
  Assert(!command_line_parsed);
  command_line_parsed = true;

  for (size_t aind = 1; aind < (size_t) argc; aind++) {
    const char *arg = argv[aind];
    if (*arg == '-') {

      // name might not be NULL-terminated
      const char *option_name = NULL;
      size_t option_name_length = 0;

      // value will be NULL-terminated
      const char *option_value = NULL;

      option_name = arg + 1;

      const char *eqpos = strchr(arg, '=');
      if (eqpos == NULL) {
        const char *nulpos = strchr(arg, 0);
        option_value = nulpos;
        option_name_length = nulpos - option_name;
      }
      else {
        option_name_length = eqpos - option_name;
        option_value = eqpos + 1;
      }

      if (option_name_length == 0) {
        cout << "ERROR: Option after '-' must have a name." << endl;
        return false;
      }

      bool found = false;
      for (size_t oind = 0; oind < options.Size(); oind++) {
        ConfigOption *o = options[oind];
        const char *oname = o->Name();

        if (strncasecmp(option_name, oname, option_name_length) == 0 &&
            oname[option_name_length] == 0) {

          if (o->IsSpecified()) {
            cout << "ERROR: Option " << oname
                 << " specified multiple times." << endl;
            return false;
          }

          if (!o->SetValue(option_value))
            return false;

          found = true;
          break;
        }
      }

      if (!found) {
        if (strcasecmp(arg, "-help") != 0)
          cout << "ERROR: Unknown option " << arg << endl;
        return false;
      }
    }
    else {
      unspecified->PushBack(arg);
    }
  }

  return true;
}

void Config::PrintUsage(const char *usage)
{
  cout << "USAGE: " << usage << endl;
  cout << "OPTIONS: " << endl;
  for (size_t oind = 0; oind < options.Size(); oind++)
    options[oind]->Print();
}

NAMESPACE_XGILL_END
