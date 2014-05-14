
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

// portions of stream.h for output streams.

#include <string.h>  // strlen
#include <errno.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

// special tokens that can appear in an output stream.

struct OutStreamEndl {};
extern OutStreamEndl endl;

struct OutStreamFlush {};
extern OutStreamFlush flush;

// abstract superclass of all output streams.
class OutStream
{
 public:
  // virtual methods which need to be overridden by subclasses.

  // append a buffer of characters to the end of this stream.
  virtual void Put(const void *buf, size_t len) = 0;

  // flush this stream.
  virtual void Flush() {}

  // output streams might have to close things down when they go away.
  virtual ~OutStream() {}

 public:
  // other helper methods.

  // append a single character to the end of this stream.
  void PutChar(uint8_t c) {
    Put(&c, 1);
  }

  // append a NULL-terminated string to the end of this stream
  // (excluding the trailing NULL).
  void PutString(const char *buf) {
    Put(buf, strlen(buf));
  }

 public:
  // stream operator methods (<<)

  OutStream& operator<< (OutStreamEndl) {
    PutString("\n");
    return *this;
  }

  OutStream& operator<< (OutStreamFlush) {
    Flush();
    return *this;
  }

  OutStream& operator<< (bool val) {
    if (val)
      PutString("true");
    else
      PutString("false");
    return *this;
  }

  OutStream& operator<< (short val) {
    sprintf(scratch, "%hd", val);
    PutString(scratch);
    return *this;
  }

  OutStream& operator<< (unsigned short val) {
    sprintf(scratch, "%hu", val);
    PutString(scratch);
    return *this;
  }

  OutStream& operator<< (int val) {
    sprintf(scratch, "%d", val);
    PutString(scratch);
    return *this;
  }

  OutStream& operator<< (unsigned int val) {
    sprintf(scratch, "%u", val);
    PutString(scratch);
    return *this;
  }

  OutStream& operator<< (long val) {
    sprintf(scratch, "%ld", val);
    PutString(scratch);
    return *this;
  }

  OutStream& operator<< (unsigned long val) {
    sprintf(scratch, "%lu", val);
    PutString(scratch);
    return *this;
  }

  OutStream& operator<< (long long val) {
    // TODO: fix overflow case.
    if (val == (long long) (long) val) {
      sprintf(scratch, "%ld", (long) val);
    }
    else {
      strcpy(scratch, "XOFLOWX");
    }
    PutString(scratch);
    return *this;
  }

  OutStream& operator<< (unsigned long long val) {
    // TODO: fix overflow case.
    if (val == (unsigned long long) (unsigned long) val) {
      sprintf(scratch, "%lu", (unsigned long) val);
    }
    else {
      strcpy(scratch, "XOFLOWX");
    }
    PutString(scratch);
    return *this;
  }

  OutStream& operator<< (float val) {
    sprintf(scratch, "%.2g", val);
    PutString(scratch);
    return *this;
  }

  OutStream& operator<< (double val) {
    sprintf(scratch, "%.2g", val);
    PutString(scratch);
    return *this;
  }

  OutStream& operator<< (long double val) {
    sprintf(scratch, "%.2Lg", val);
    PutString(scratch);
    return *this;
  }

  OutStream& operator<< (void *val) {
    sprintf(scratch, "%p", val);
    PutString(scratch);
    return *this;
  }

 public:
  // std::ostream methods we are replicating.

  void flush() { Flush(); }
  OutStream& write(const char *s, size_t n) {
    Put(s, n);
    return *this;
  }

 private:
  // this buffer needs to be big enough to accomodate the string
  // version of any integer or floating point value.
  char scratch[200];
};

// additional global operators on chars and strings.

inline OutStream& operator<< (OutStream& out, char c) {
  out.PutChar(c);
  return out;
}

inline OutStream& operator<< (OutStream& out, signed char c) {
  out.PutChar((char) c);
  return out;
}

inline OutStream& operator<< (OutStream& out, unsigned char c) {
  out.PutChar((char) c);
  return out;
}

inline OutStream& operator<< (OutStream& out, const char *s) {
  out.PutString(s);
  return out;
}

inline OutStream& operator<< (OutStream& out, const signed char *s) {
  out.PutString((const char*) s);
  return out;
}

inline OutStream& operator<< (OutStream& out, const unsigned char *s) {
  out.PutString((const char*) s);
  return out;
}

// alias for code using std::ostream.
typedef OutStream ostream;

// output stream for either standard out or standard error.
class PrintOutStream : public OutStream {
 public:

  // the file is either stdout or stderr.
  PrintOutStream(FILE *file)
    : m_file(file)
  {}

  // inherited methods.

  virtual void Put(const void *buf, size_t len) {
    size_t count = fwrite(buf, 1, len, m_file);
    if (count != len)
      printf("ERROR: PrintOutStream::Put failure: %d\n", errno);
  }

  virtual void Flush() {
    fflush(m_file);
  }

 private:

  // underlying file descriptor.
  FILE *m_file;
};

// the usual cout/cerr streams. the main drawback with these is that they
// can't be used during static initialization; even if all members are
// removed from PrintOutStream, the vtable for these might not be initialized
// properly by the time cout/cerr/clog is used. (it would be nice if uses
// of the vtable were optimized away, as the Put/Flush methods are final
// in PrintOutStream, but tis not to be).
extern PrintOutStream cout;
extern PrintOutStream cerr;
extern PrintOutStream clog;  // alias for cerr.

// output stream for writing to a file.
class FileOutStream : public OutStream {
 public:

  // open a file for the specified name and make an output stream for it.
  // closes the file on deletion.
  FileOutStream(const char *name)
    : m_file(NULL)
  {
    m_file = fopen(name, "w");
    if (m_file == NULL) {
      printf("ERROR: FileOutStream::Open failure: %d\n", errno);
    }
  }

  // make an invalid file output stream.
  FileOutStream()
    : m_file(NULL)
  {}

  // close the underlying file down if necessary.
  ~FileOutStream() {
    if (m_file)
      fclose(m_file);
  }

  // whether this stream has encountered an error.
  bool IsError() { return m_file == NULL; }

  // inherited methods.

  virtual void Put(const void *buf, size_t len) {
    if (m_file) {
      size_t count = fwrite(buf, 1, len, m_file);
      if (count != len) {
        printf("ERROR: FileOutStream::Put failure: %d\n", errno);
        fclose(m_file);
        m_file = NULL;
      }
    }
    else {
      printf("ERROR: FileOutStream::Put on bad file\n");
    }
  }

  virtual void Flush() {
    if (m_file) {
      int ret = fflush(m_file);
      if (ret != 0) {
        printf("ERROR: FileOutStream::Flush failure: %d\n", errno);
        fclose(m_file);
        m_file = NULL;
      }
    }
    else {
      printf("ERROR: FileOutStream::Flush on bad file\n");
    }
  }

 private:

  // underlying file descriptor.
  FILE *m_file;
};

// alias for code using std::ofstream
typedef FileOutStream ofstream;

// the active logging stream. pretty much all output should go here.
extern OutStream *log_stream;

// write to the logging stream.
#define logout (*log_stream)

// write to the logging stream without using an OutStream.
#define logfile stdout

// see BufferOutStream in buffer.h for a stream that appends to a char buffer.
