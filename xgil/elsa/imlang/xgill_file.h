// xgill_file.h        see license.txt for copyright and terms of use
// source/preprocessed code handling for xgill frontend.

#pragma once

#include <util/buffer.h>

// filename setup.

// do initial processing of the input preprocessed file, reading its
// preprocessed and original source code into the databases and setting
// the compiler working directory. return value is whether the input file
// is a C++ source file (vs. C file), as determined from the file name
// and/or preprocessor #line directives.
bool ProcessInputFileContents(const char *input_file);

// filename manipulation.

// functionality for dumping original and preprocessed source files
// to databases for later use by the UI.

// database to receive contents of source files.
#define SOURCE_DATABASE "file_source.xdb"

// database to receive contents of preprocessed files.
#define PREPROC_DATABASE "file_preprocess.xdb"
