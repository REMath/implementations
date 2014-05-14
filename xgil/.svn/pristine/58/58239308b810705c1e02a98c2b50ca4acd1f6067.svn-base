// fileloc.cc            see license.txt for copyright and terms of use
// code for fileloc.h

#include "fileloc.h"       // this module
#include "flatten.h"       // Flatten

#include <string.h>        // streq


// -------------------- FileLocation -----------------------------
void FileLocation::xfer(Flatten &flat)
{
  flat.xferInt(line);
  flat.xferInt(col);
}


string FileLocation::toString() const
{
  if (validLoc()) {
    return stringc << "line " << line << ", col " << col;
  }
  else {
    return string("(unknown loc)");
  }
}


void FileLocation::advance(char const *text, int length)
{ 
  // can't advance an invalid location
  xassert(validLoc());

  char const *p = text;
  char const *endp = text + length;
  for (; p < endp; p++) {
    if (*p == '\n') {      // new line
      line++;
      col = 1;
    }
    else {	      	   // ordinary character
      col++;
    }
  }
}


void FileLocation::newLine()
{
  // can't advance an invalid location
  xassert(validLoc());

  line++;
  col = firstColumn;
}


// ------------------- SourceFile --------------------
SourceFile::~SourceFile()
{}


// ------------------- SourceLocation --------------------
void SourceLocation::xfer(Flatten &flat)
{
  if (flat.writing()) { 
    char *str = file? file->filename.pchar() : NULL;
    flat.xferCharString(str);
  }

  else { // reading
    char *str;
    flat.xferCharString(str);

    if (!str) {
      file = NULL;
    }
    else {
      // not null; allocate a new (if necessary) object in the global list
      file = sourceFileList.open(str);
      delete[] str;
    }
  }
}


char const *SourceLocation::fname() const
{ 
  if (file) {
    return file->filename;
  }
  else {
    return NULL;
  }
}

string SourceLocation::oldToString() const
{
  if (fname()) {
    return stringc << "file " << fname() << ", "
                   << FileLocation::toString();
  }
  else {
    return FileLocation::toString();
  }
}

string SourceLocation::likeGccToString() const
{
  if (validLoc()) {
    return stringc << fname() << ":" << line << ":" << col;
  }
  else {
    return string("(?loc?)");
  }
}


// ------------------- SourceFileList -----------------
SourceFileList::SourceFileList()
{}

SourceFileList::~SourceFileList()
{}


SourceFile *SourceFileList::open(char const *fname)
{
  // check for an existing SourceFile
  MUTATE_EACH_OBJLIST(SourceFile, files, iter) {
    if (streq(iter.data()->filename, fname)) {
      // found match
      return iter.data();
    }
  }

  // make a new one
  SourceFile *ret = new SourceFile(fname);
  files.append(ret);
  return ret;
}


// the global list
// (not thread-safe)
SourceFileList sourceFileList;
