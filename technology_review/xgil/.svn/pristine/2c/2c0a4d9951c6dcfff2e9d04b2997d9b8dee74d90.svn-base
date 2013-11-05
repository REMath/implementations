// parsetables.cc            see license.txt for copyright and terms of use
// code for parsetables.h

#include "parsetables.h"    // this module
#include "bflatten.h"       // BFlatten
#include "trace.h"          // traceProgress
#include "crc.h"            // crc32
#include "emitcode.h"       // EmitCode
#include "bit2d.h"          // Bit2d

#include <string.h>         // memset
#include <stdlib.h>         // qsort, system


// array index code
enum { UNASSIGNED = -1 };

               
// fwd
template <class EltType>
void printTable(EltType const *table, int size, int rowLength,
                rostring typeName, rostring tableName);


ParseTables::ParseTables(int t, int nt, int s, int p, int et, StateId start, int final)
{
  alloc(t, nt, s, p, et, start, final);
}
    
template <class T>
void allocInitArray(T *&arr, int size, T init)
{
  arr = new T[size];
  for (int i=0; i<size; i++) {
    arr[i] = init;
  }
}

template <class T>
void allocZeroArray(T *&arr, int size)
{
  arr = new T[size];
  memset(arr, 0, sizeof(arr[0]) * size);
}

void ParseTables::alloc(int t, int nt, int s, int p, int et, StateId start, int final)
{
  owning = true;

  temp = new TempData(s);

  numTerms = t;
  numNonterms = nt;
  numStates = s;
  numProds = p;

  errorTerm = et;

  actionCols = numTerms;
  actionRows = numStates;

  gotoCols = numNonterms;
  gotoRows = numStates;

  errorCols = numTerms;
  errorRows = numStates;

  allocZeroArray(actionTable, actionTableSize());
  allocZeroArray(gotoTable, gotoTableSize());
  allocZeroArray(errorTable, errorTableSize());

  allocZeroArray(prodInfo, numProds);
  allocZeroArray(stateSymbol, numStates);

  // table of ambiguous actions is NULL until someone fills in the
  // whole thing; since we don't know how many there might be, we
  // can't even allocate the storage now
  ambigTableSize = 0;
  ambigTable = NULL;

  startState = start;
  finalProductionIndex = final;

  allocZeroArray(nontermOrder, nontermOrderSize());
}


ParseTables::~ParseTables()
{
  if (temp) {
    delete temp;
  }

  if (owning) {
    delete[] actionTable;
    delete[] gotoTable;
    delete[] errorTable;
    delete[] prodInfo;
    delete[] stateSymbol;

    if (ambigTable) {
      delete[] ambigTable;
    }

    delete[] nontermOrder;
  }
}


ParseTables::TempData::TempData(int numStates)
  : ambigTable(),
    bigProductionList(),
    productionsForState(numStates),
    ambigStateTable(numStates)
{
  productionsForState.setAll(UNASSIGNED);
  ambigStateTable.setAll(UNASSIGNED);
}

ParseTables::TempData::~TempData()
{}


ActionEntry ParseTables::validateAction(int code) const
{
  // make sure that 'code' is representable; if this fails, most likely
  // there are more than 32k states or productions; in turn, the most
  // likely cause of *that* would be the grammar is being generated
  // automatically from some other specification; you can change the
  // typedefs of ActionEntry and GotoEntry in gramanl.h to get more
  // capacity
  ActionEntry ret = (ActionEntry)code;
  xassert((int)ret == code);
  return ret;
}

GotoEntry ParseTables::validateGoto(int code) const
{
  // see above
  GotoEntry ret = (GotoEntry)code;
  xassert((int)ret == code);
  xassert(ret != errorGotoEntry);    // otherwise collision with error code
  return ret;
}


// doesn't init anything; for use by emitConstructionCode's emitted code
ParseTables::ParseTables(bool o)
  : owning(o),
    temp(NULL)
{
  xassert(owning == false);
}

ActionEntry ParseTables::encodeShift(StateId destState)
{
  return validateAction(+destState+1);
}


ActionEntry ParseTables::encodeReduce(int prodId)
{
  return validateAction(-prodId-1);
}


ActionEntry ParseTables::encodeAmbig(ArrayStack<ActionEntry> const &set)
{
  int end = temp->ambigTable.length();
  appendAmbig(set);
  return validateAction(numStates+end+1);
}


void ParseTables::appendAmbig(ArrayStack<ActionEntry> const &set)
{
  temp->ambigTable.push(set.length());
  for (int j=0; j < set.length(); j++) {
    temp->ambigTable.push(set[j]);
  }
}

bool ParseTables::compareAmbig(ArrayStack<ActionEntry> const &set,
                               int startIndex)
{
  if (temp->ambigTable[startIndex] != set.length()) {
    return false;           // mismatch in 1st entry
  }
  for (int j=0; j < set.length(); j++) {
    if (temp->ambigTable[startIndex+1+j] != set[j]) {
      return false;         // mismatch in j+2nd entry
    }
  }
  return true;              // match!
}


ActionEntry ParseTables::encodeError() const
{
  return validateAction(0);
}


GotoEntry ParseTables::encodeGoto(StateId destState, int shiftedNontermId) const
{
  return validateGoto(destState);
}


// simple alloc + copy
template <class T>
void copyArray(int &len, T *&dest, ArrayStack<T> const &src)
{
  len = src.length();
  dest = new T[len];
  memcpy(dest, src.getArray(), sizeof(T) * len);
}

// given an array 'src' of indices relative to 'base', allocate the
// array 'dest' and fill it in with actual pointers into 'base'
template <class T>
void copyIndexPtrArray(int len, T **&dest, T *base, ArrayStack<int> const &src)
{
  dest = new T* [len];
  for (int i=0; i<len; i++) {          
    if (src[i] != UNASSIGNED) {
      dest[i] = base + src[i];
    }
    else {
      dest[i] = NULL;      // so segfault if deref unassigned entry
    }
  }
}

void ParseTables::finishTables()
{
  // copy the ambiguous actions
  copyArray(ambigTableSize, ambigTable, temp->ambigTable);

  delete temp;
  temp = NULL;
}


static int intCompare(void const *left, void const *right)
{
  return *((int const*)left) - *((int const*)right);
}



// --------------------- table emission -------------------
// create literal tables
template <class EltType>
void emitTable(EmitCode &out, EltType const *table, int size, int rowLength,
               rostring typeName, rostring tableName)
{
  if (!table || !size) {
    out << "  " << typeName << " *" << tableName << " = NULL;\n";
    return;
  }

  bool printHex = 0==strcmp(typeName, "ErrorBitsEntry");
  bool needCast = 0==strcmp(typeName, "StateId");

  if (size * sizeof(*table) > 50) {    // suppress small ones
    out << "  // storage size: " << size * sizeof(*table) << " bytes\n";
    if (size % rowLength == 0) {
      out << "  // rows: " << (size/rowLength) << "  cols: " << rowLength << "\n";
    }
  }

  int rowNumWidth = stringf("%d", size / rowLength /*round down*/).length();

  // I make tables 'const' because that way the OS loader might be
  // smart enough to share them (on a read-only basis) across multiple
  // processes started from the same executable.  But I immediately
  // cast them to non-const, since ParseTables doesn't declare
  // pointers-to-const (since it also has methods to modify the tables
  // at parser generation time).

  out << "  static " << typeName << " const " << tableName << "[" << size << "] = {";
  int row = 0;
  for (int i=0; i<size; i++) {
    if (i % rowLength == 0) {    // one row per state
      out << stringf("\n    /""*%*d*""/ ", rowNumWidth, row++);
    }

    if (needCast) {
      out << "(" << typeName << ")";
    }

    if (printHex) {
      out << stringf("0x%02X, ", table[i]);
    }
    else if (sizeof(table[i]) == 1) {
      // little bit of a hack to make sure 'unsigned char' gets
      // printed as an int; the casts are necessary because this
      // code gets compiled even when EltType is ProdInfo
      out << (int)(*((unsigned char*)(table+i))) << ", ";
    }
    else {
      // print the other int-sized things, or ProdInfo using
      // the overloaded '<<' below
      out << table[i] << ", ";
    }
  }
  out << "\n"
      << "  };\n";
}

// used to emit the elements of the prodInfo table
stringBuilder& operator<< (stringBuilder &sb, ParseTables::ProdInfo const &info)
{
  sb << "{" << (int)info.rhsLen << "," << (int)info.lhsIndex << "}";
  return sb;
}


// like 'emitTable', but also set a local called 'tableName'
template <class EltType>
void emitTable2(EmitCode &out, EltType const *table, int size, int rowLength,
                rostring typeName, rostring tableName)
{
  string tempName = stringc << tableName << "_static";
  emitTable(out, table, size, rowLength, typeName, tempName);
  out << "  " << tableName << " = const_cast<" << typeName << "*>(" 
      << tempName << ");\n\n";
}


template <class EltType>
void emitOffsetTable(EmitCode &out, EltType **table, EltType *base, int size,
                     rostring typeName, rostring tableName, rostring baseName)
{
  if (!table) {
    out << "  " << tableName << " = NULL;\n\n";
    return;
  }

  // make the pointers persist by storing a table of offsets
  Array<int> offsets(size);
  bool allUnassigned = true;
  for (int i=0; i < size; i++) {
    if (table[i]) {
      offsets[i] = table[i] - base;
      allUnassigned = false;
    }
    else {
      offsets[i] = UNASSIGNED;    // codes for a NULL entry
    }
  }

  if (allUnassigned) {
    // for example, an LALR(1) grammar has no ambiguous entries in its tables
    size = 0;
  }

  if (size > 0) {
    out << "  " << tableName << " = new " << typeName << " [" << size << "];\n";

    emitTable(out, (int*)offsets, size, 16, "int", stringc << tableName << "_offsets");

    // at run time, interpret the offsets table
    out << "  for (int i=0; i < " << size << "; i++) {\n"
        << "    int ofs = " << tableName << "_offsets[i];\n"
        << "    if (ofs >= 0) {\n"
        << "      " << tableName << "[i] = " << baseName << " + ofs;\n"
        << "    }\n"
        << "    else {\n"
        << "      " << tableName << "[i] = NULL;\n"
        << "    }\n"
        << "  }\n\n";
  }
  else {
    out << "  // offset table is empty\n"
        << "  " << tableName << " = NULL;\n\n";
  }
}

                
// for debugging
template <class EltType>
void printTable(EltType const *table, int size, int rowLength,
                rostring typeName, rostring tableName)
{            
  // disabled for now since I don't need it anymore, and it adds
  // a link dependency on emitcode.cc ...
  #if 0
  {
    EmitCode out("printTable.tmp");
    emitTable(out, table, size, rowLength, typeName, tableName);
  }

  system("cat printTable.tmp; rm printTable.tmp");
  #endif // 0
}


// emit code for a function which, when compiled and executed, will
// construct this same table (except the constructed table won't own
// the table data, since it will point to static program data)
void ParseTables::emitConstructionCode(EmitCode &out,
  rostring className, rostring funcName)
{
  // must have already called 'finishTables'
  xassert(!temp);

  out << "// this makes a ParseTables from some literal data;\n"
      << "// the code is written by ParseTables::emitConstructionCode()\n"
      << "// in " << __FILE__ << "\n"
      << "class " << className << "_ParseTables : public ParseTables {\n"
      << "public:\n"
      << "  " << className << "_ParseTables();\n"
      << "};\n"
      << "\n"
      << className << "_ParseTables::" << className << "_ParseTables()\n"
      << "  : ParseTables(false /*owning*/)\n"
      << "{\n"
      ;

  // set all the integer-like variables
  #define SET_VAR(var) \
    out << "  " #var " = " << var << ";\n";
  SET_VAR(numTerms);
  SET_VAR(numNonterms);
  SET_VAR(numStates);
  SET_VAR(numProds);
  SET_VAR(errorTerm);
  SET_VAR(actionCols);
  SET_VAR(actionRows);
  SET_VAR(gotoCols);
  SET_VAR(gotoRows);
  SET_VAR(errorCols);
  SET_VAR(errorRows);
  SET_VAR(ambigTableSize);
  out << "  startState = (StateId)" << (int)startState << ";\n";
  SET_VAR(finalProductionIndex);
  #undef SET_VAR
  out << "\n";

  // action table, one row per state
  emitTable2(out, actionTable, actionTableSize(), actionCols,
             "ActionEntry", "actionTable");

  // goto table, one row per state
  emitTable2(out, gotoTable, gotoTableSize(), gotoCols,
             "GotoEntry", "gotoTable");

  // error table, one row per state
  emitTable2(out, errorTable, errorTableSize(), errorCols,
             "ErrorEntry", "errorTable");

  // production info, arbitrarily 16 per row
  emitTable2(out, prodInfo, numProds, 16, "ParseTables::ProdInfo", "prodInfo");

  // state symbol map, arbitrarily 16 per row
  emitTable2(out, stateSymbol, numStates, 16, "SymbolId", "stateSymbol");

  // ambigTable
  emitTable2(out, ambigTable, ambigTableSize, 16, "ActionEntry", "ambigTable");

  // nonterminal order
  emitTable2(out, nontermOrder, nontermOrderSize(), 16,
             "NtIndex", "nontermOrder");

  out << "}\n"
      << "\n"
      << "\n"
      << "ParseTables *" << className << "::" << funcName << "()\n"
      << "{\n"
      << "  return new " << className << "_ParseTables;\n"
      << "}\n"
      << "\n"
      ;
}


// EOF
