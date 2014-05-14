// fileloc.h            see license.txt for copyright and terms of use
// data structures for recording character positions in files

#ifndef __FILELOC_H
#define __FILELOC_H

// I'm replacing all uses of this module with srcloc.h, but for
// the time being I'll leave fileloc.h in the repository.
#error do not use me, use srcloc.h instead

#include "str.h"       // string
#include "objlist.h"   // ObjList

class Flatten;

// identifies a location in a source file
class FileLocation {
public:
  enum Constants {
    // I pick 1,1 as my upper left, since it's traditional to number
    // lines at 1, and 1,1 is nicer than 0,1 as an origin; I modified
    // emacs' sources to display 1-based columns on my system..
    firstColumn = 1,               // number of first column
    firstLine = 1,                 // number of first line

    invalid = -1,                  // no useful value known
  };

  int line;    // line #, 1-based
  int col;     // column #, 1-based

public:
  FileLocation()                          : line(invalid), col(invalid) {}
  FileLocation(int l, int c)              : line(l), col(c) {}
  FileLocation(FileLocation const &obj)	  : line(obj.line), col(obj.col) {}
  ~FileLocation()                         {}

  FileLocation(Flatten&)                  {}
  void xfer(Flatten &flat);

  FileLocation& operator= (FileLocation const &obj)
    { line=obj.line; col=obj.col; return *this; }

  bool validLoc() const { return line != invalid; }

  void reset() { line=firstLine; col=firstColumn; }

  // "line %d, col %d"
  string toString() const;

  // move forward to reflect location after 'text'
  void advance(char const *text, int length);

  // wrap to the next line
  void newLine();
};


// names a source file
// (will get bigger; mostly a placeholder for now)
class SourceFile {
public:
  string filename;

public:
  SourceFile(char const *fn) : filename(fn) {}
  ~SourceFile();
};


// position in file, and pointer to which file
class SourceLocation : public FileLocation {
public:
  SourceFile *file;         // (serf)

public:
  SourceLocation(SourceFile *f = NULL) : file(f) {}
  SourceLocation(FileLocation const &floc, SourceFile *f)
    : FileLocation(floc),
      file(f)
  {}
  SourceLocation(SourceLocation const &obj)
    : FileLocation(obj),
      file(obj.file)
  {}
  ~SourceLocation() {}

  SourceLocation(Flatten&) {}
  void xfer(Flatten &flat);

  SourceLocation& operator= (SourceLocation const &obj)
  {
    FileLocation::operator=(obj);
    file = obj.file;
    return *this;
  }

  // can return NULL
  char const *fname() const;

  // "file %s, line %d, col %d"
  string oldToString() const;

  // "<file>:<line>:<col>", or "" if no loc info
  string likeGccToString() const;

  string toString() const { return likeGccToString(); }

  friend stringBuilder& operator<< (stringBuilder &sb, SourceLocation const &obj)
    { return sb << obj.toString(); }
  friend ostream& operator<< (ostream &os, SourceLocation const &obj)
    { return os << obj.toString(); }
};

inline string toString(SourceLocation const &loc)
  { return loc.toString(); }


// global list of files processed; expectation is tools toss
// files in here when opened and use the resulting pointer to
// refer to the file, even after it's closed
class SourceFileList {
private:     // data
  ObjList<SourceFile> files;
  
public:
  SourceFileList();
  ~SourceFileList();

  // get permanent name for a file; if you call open twice
  // with the same name (case sensitive), it will return the
  // same structure as before
  SourceFile * /*serf*/ open(char const *fname);

  // clear all files
  void clear() { files.deleteAll(); }
};

// the global list
extern SourceFileList sourceFileList;


// macro for obtaining a source location that points at the 
// point in the source code where this macro is invoked
#define HERE_SOURCELOCATION                        \
  SourceLocation(FileLocation(__LINE__, 1),        \
                 sourceFileList.open(__FILE__))


#endif // __FILELOC_H
