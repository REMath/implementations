// xgill_file.cc        see license.txt for copyright and terms of use
// source/preprocessed code handling for xgill frontend.

#include "xgill_file.h"
#include <backend/backend_compound.h>

// we don't pull in any Elsa stuff here so we don't have naming conflicts.
NAMESPACE_XGILL_USING

// this hooks into g_normalize_directory from the Elsa lexer.
ConfigOption source_directory(CK_String, "source-directory", ".",
                      "Root build directory for relative path names");

// pull in references to these without pulling in all the Elsa stuff.
extern char *g_working_directory;
extern char *g_normalize_directory;
extern char* GetNormalizedFile(const char *file);

extern ConfigOption annotate;

void SetInputFile(const char *input_file)
{
  Assert(g_working_directory == NULL);
  Assert(g_normalize_directory == NULL);

  // see if there is a normalize directory to use.
  if (source_directory.IsSpecified())
    g_normalize_directory = strdup(source_directory.StringValue());

  // check for a .info file specifying the build's working directory.
  Buffer info_file;
  info_file.Append(input_file, strlen(input_file));
  info_file.Append(".info", sizeof(".info"));

  ifstream info_in((const char*) info_file.base);

  if (!info_in.IsError()) {
    Buffer info_data;
    ReadInStream(info_in, &info_data);

    Vector<char*> lines;
    SplitBufferStrings(&info_data, '\n', &lines);

    if (lines.Size() >= 1)
      g_working_directory = strdup(lines[0]);
  }
}

// return whether the specified file is C++ or not. it should have one
// of the following extensions: .c, .cpp, .cc, .cxx. warns on other
// extensions and treats them as C++.
bool IsFileCPP(const char *file)
{
  // find the position of the extension.
  const char *dot_pos = file;

  while (true) {
    const char *next_dot_pos = strchr(dot_pos, '.');
    if (next_dot_pos == NULL)
      break;
    dot_pos = next_dot_pos + 1;
  }

  if (strcmp(dot_pos, "c") == 0)
    return false;

  if (strcmp(dot_pos, "cpp") == 0)
    return true;

  if (strcmp(dot_pos, "cc") == 0)
    return true;

  if (strcmp(dot_pos, "cxx") == 0)
    return true;

  cout << "WARNING: Unrecognized source file extension: " << file << endl;
  return true;
}

// hash storing files which have been processed by a worker already.
#define PROCESSED_FILES_HASH  "processed_files_hash"

// data read so far about a preprocessed file. this excludes the filename,
// which is the key in the table this data is stored in.
struct FileData
{
  // contents of the preprocessed file, pieced together from all the places
  // a # line directive appeared for that file.
  Buffer *contents;

  // line number of the next line that will be added for this file.
  // this is equal to the number of '\n' in the contents buffer + 1.
  size_t cur_line;

  // receives transaction result indicating whether this file has already
  // been added to the preprocessed database.
  size_t processed_var;

  FileData()
    : contents(NULL), cur_line(0), processed_var(0)
  {}
};

typedef HashTable<String*,FileData,String>
  FileDataTable;

class QueryFileData : public HashTableVisitor<String*,FileData>
{
public:
  Transaction *t;

  QueryFileData(Transaction *_t)
    : t(_t)
  {}

  void Visit(String *&file, Vector<FileData> &data_list)
  {
    Assert(data_list.Size() == 1);

    size_t var = t->MakeVariable(true);
    data_list[0].processed_var = var;

    TOperand *key_arg = new TOperandString(t, file->Value());

    t->PushAction(
      Backend::HashIsMember(t, PROCESSED_FILES_HASH, key_arg, var));
    t->PushAction(
      Backend::HashInsertKey(t, PROCESSED_FILES_HASH, key_arg));
  }
};

// scratch buffer for reading file contents.
static Buffer scratch_buf;

class DumpFileData : public HashTableVisitor<String*,FileData>
{
public:
  Transaction *query;
  Transaction *t;
 
  DumpFileData(Transaction *_query, Transaction *_t)
    : query(_query), t(_t)
  {}

  void Visit(String *&file, Vector<FileData> &data_list)
  {
    Assert(data_list.Size() == 1);
    FileData data = data_list[0];

    TOperandBoolean *var_res = query->LookupBoolean(data.processed_var);
    if (!var_res->IsTrue()) {
      const char *file_name = file->Value();
      TOperand *key_arg = new TOperandString(t, file_name);

      // compress and store the preprocessed file contents.
      TOperandString *preproc_arg = TOperandString::Compress(t, data.contents);
      t->PushAction(
        Backend::XdbReplace(t, PREPROC_DATABASE, key_arg, preproc_arg));

      // don't look for the source for special compiler files.
      if (file_name[0] == '<')
        return;

      // try to reconstruct the absolute filename from the normalized name.
      Buffer abs_name;
      if (g_normalize_directory && file_name[0] != '/') {
        abs_name.Append(g_normalize_directory, strlen(g_normalize_directory));
        abs_name.Append("/", 1);
      }
      abs_name.Append(file_name, strlen(file_name) + 1);

      const char *abs_cstr = (const char*) abs_name.base;

      // compress and store the source file contents.
      FileInStream file_in(abs_cstr);
      if (file_in.IsError()) {
        cout << "WARNING: Could not find source file: " << abs_cstr << endl;
      }
      else {
        ReadInStream(file_in, &scratch_buf);

        TOperandString *source_arg = TOperandString::Compress(t, &scratch_buf);
        t->PushAction(
          Backend::XdbReplace(t, SOURCE_DATABASE, key_arg, source_arg));

        scratch_buf.Reset();
      }
    }
  }
};

class ClearFileData : public HashTableVisitor<String*,FileData>
{
  void Visit(String *&file, Vector<FileData> &data_list)
  {
    file->DecRef(&data_list);

    Assert(data_list.Size() == 1);
    Assert(data_list[0].contents);
    delete data_list[0].contents;
  }
};

bool ProcessInputFileContents(const char *input_file)
{
  SetInputFile(input_file);

  // skip input file processing for annotation input files.
  // for now these are all treated as C++ files.
  if (annotate.IsSpecified())
    return true;

  Buffer file_buf;

  // read the entire contents of the file into the buffer.
  {
    ifstream file_in(input_file);
    ReadInStream(file_in, &file_buf);
  }

  // table with contents read so far for 
  FileDataTable file_table;

  // name of the original file which was being parsed, from which we will
  // get whether this is a C or a C++ file.
  const char *base_file = NULL;

  char *pos = (char*) file_buf.base;

  FileData *cur_data = NULL;
  while (*pos) {

    if (*pos == '#' && *(pos+1) == ' ') {
      // found a preprocessor line directive.
      // currently we just parse lines of the format '# line "file" ...

      // eat the '#'
      pos++;

      char *end_pos = NULL;
      long line = strtol(pos, &end_pos, 10);
      Assert(end_pos);

      char *start_quote = strchr(end_pos, '"');
      Assert(start_quote);

      char *end_quote = strchr(start_quote + 1, '"');
      Assert(end_quote);

      char *end_line = strchr(pos, '\n');
      Assert(end_line && end_line > end_quote);

      if (base_file == NULL) {
        // just mark the first # line directive we see as the base file.
        base_file = start_quote + 1;
      }

      *end_quote = 0;
      char *file_cstr = GetNormalizedFile(start_quote + 1);
      String *file = String::Make(file_cstr);
      free(file_cstr);

      Vector<FileData> *entries = file_table.Lookup(file, true);
      if (entries->Empty()) {
        file->MoveRef(NULL, entries);
        entries->PushBack(FileData());

        cur_data = &entries->Back();
        cur_data->contents = new Buffer();
        cur_data->cur_line = line;
      }
      else {
        file->DecRef();
        Assert(entries->Size() == 1);

        cur_data = &entries->Back();
        while ((long) cur_data->cur_line < line) {
          cur_data->contents->Append("\n", 1);
          cur_data->cur_line++;
        }
      }

      pos = end_line + 1;
      continue;
    }

    if (cur_data == NULL) {
      // we can get here if the input file is not actually preprocessed.
      // make data for the input file itself.

      char *file_cstr = GetNormalizedFile(input_file);
      String *file = String::Make(file_cstr);
      free(file_cstr);

      Vector<FileData> *entries = file_table.Lookup(file, true);
      Assert(entries->Empty());

      file->MoveRef(NULL, entries);
      entries->PushBack(FileData());

      cur_data = &entries->Back();
      cur_data->contents = new Buffer();
      cur_data->cur_line = 1;
    }

    char *end_line = strchr(pos, '\n');
    if (end_line == NULL) {
      cur_data->contents->Append(pos, strlen(pos));
      break;
    }

    cur_data->contents->Append(pos, end_line - pos + 1);
    cur_data->cur_line++;

    pos = end_line + 1;
  }

  Transaction *query = new Transaction();
  QueryFileData query_visit(query);
  file_table.VisitEach(&query_visit);

  SubmitTransaction(query);

  Transaction *dump = new Transaction();
  DumpFileData dump_visit(query, dump);
  file_table.VisitEach(&dump_visit);

  SubmitTransaction(dump);

  delete query;
  delete dump;

  ClearFileData clear_visit;
  file_table.VisitEach(&clear_visit);

  if (base_file)
    return IsFileCPP(base_file);

  // if there were no # line directives (the file was not preprocessed)
  // use the extension on the input file itself.
  return IsFileCPP(input_file);
}
