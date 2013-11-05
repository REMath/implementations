
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

// portions of stream.h for input streams.

#include <string.h>  // strlen
#include <errno.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

// abstract class of all input streams.
class InStream
{
 public:
  InStream()
    : m_last_count(0)
  {}

 public:
  // virtual methods which need to be overridden by subclasses.

  // read as much of the stream as is available and put the data in buf,
  // up to len bytes. return the number of bytes read.
  virtual size_t Get(void *buf, size_t len) = 0;

  // return whether this stream has reached the end of its input.
  virtual bool IsEOF() = 0;

  // return whether the stream is in an error state.
  virtual bool IsError() { return false; }

  // input streams might have to close things down when they go away.
  virtual ~InStream() {}

 public:
  // std::istream methods we are replicating.

  bool eof() { return IsEOF(); }
  bool fail() { return IsError(); }
  bool bad() { return false; }

  InStream& get(char &c) {
    m_last_count = Get(&c, 1);
    return *this;
  }

  InStream& read(char *s, size_t n) {
    m_last_count = Get(s, n);
    return *this;
  }

  size_t gcount() {
    return m_last_count;
  }

 private:
  // count of last istream operation for gcount()
  size_t m_last_count;
};

// alias for modules based on std::istream.
typedef InStream istream;

// input stream for reading from cin.
class PrintInStream : public InStream
{
 public:
  // file can only really be stdin.
  PrintInStream(FILE *file)
    : m_file(file)
  {}

  // inherited methods.

  size_t Get(void *buf, size_t len) {
    return fread(buf, 1, len, m_file);
  }

  bool IsEOF() {
    return feof(m_file);
  }

 private:
  FILE *m_file;
};

extern PrintInStream cin;

// input stream for reading from a file.
class FileInStream : public InStream
{
 public:
  FileInStream(const char *name)
    : m_file(NULL)
  {
    // OK for file to be NULL here if the file doesn't exist.
    m_file = fopen(name, "r");
  }

  // close the underlying file down if necessary.
  ~FileInStream() {
    if (m_file)
      fclose(m_file);
  }

  // whether this stream has encountered an error.
  bool IsError() { return m_file == NULL; }

  // inherited methods.

  size_t Get(void *buf, size_t len) {
    if (m_file) {
      return fread(buf, 1, len, m_file);
    }
    else {
      printf("ERROR: FileInStream::Get on a bad file\n");
      return 0;
    }
  }

  bool IsEOF() {
    if (m_file)
      return feof(m_file);
    else
      return true;
  }

 private:
  FILE *m_file;
};

// alias for modules based on std::ifstream.
typedef FileInStream ifstream;

// input stream for reading from a string.
class StringInStream : public InStream
{
 public:
  StringInStream(const char *str)
    : m_str(str), m_len(strlen(str)), m_eof(false)
  {}

  StringInStream(const char *str, size_t len)
    : m_str(str), m_len(len), m_eof(false)
  {}

  // inherited methods.

  size_t Get(void *buf, size_t len) {
    if (m_len == 0) {
      m_eof = true;
      return 0;
    }
    else if (m_len < len) {
      m_eof = true;
      size_t copied = m_len;
      memcpy(buf, m_str, m_len);
      m_str += m_len;
      m_len = 0;
      return copied;
    }
    else {
      memcpy(buf, m_str, len);
      m_str += len;
      m_len -= len;
      return len;
    }
  }

  bool IsEOF() { return m_eof; }

 private:
  // advanced as we consume parts of the input.
  const char *m_str;

  // remaining characters until the NULL terminator.
  size_t m_len;

  // set when we have tried to read in the NULL terminator.
  // if this is set then m_len is zero, but not necessarily the converse.
  bool m_eof;
};

