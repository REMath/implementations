
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

// filename normalization and generation of source/preprocessed databases.

#include <util/assert.h>
#include <util/istream.h>

NAMESPACE_XGILL_BEGIN

// set the working directory to use in NormalizeFile. this does not
// have to be the working directory for the current process.
void SetWorkingDirectory(const char *path);

// set the base directory to use in NormalizeFile.
void SetBaseDirectory(const char *path);

// gets a normalized representation of file. file may be either
// absolute or relative from the working directory above. the normalized
// file will be relative to the base directory above, or absolute if it
// is not contained in the base directory. the result string is temporary
// and will not persist after the next NormalizeFile.
char* NormalizeFile(const char *file);

// process the contents of a preprocessor's results from in, and stores
// any necessary file source or preprocessed contents into the appropriate
// databases. if in was read from a file, input_file indicates the name of
// that file (in this case, in may not be preprocessed doce).
void ProcessPreprocessedFile(istream &in, const char *input_file);

NAMESPACE_XGILL_END
