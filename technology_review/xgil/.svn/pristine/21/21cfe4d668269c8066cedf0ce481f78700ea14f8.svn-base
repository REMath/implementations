// emitcode.h            see license.txt for copyright and terms of use
// track state of emitted code so I can emit #line too

#ifndef EMITCODE_H
#define EMITCODE_H

#include "str.h"          // stringBuffer
#include "srcloc.h"       // SourceLoc

class EmitCode : public stringBuilder {
private:     // data
  ofstream os;         // stream to write to
  string fname;        // filename for emitting #line
  int line;            // current line number

public:      // funcs
  EmitCode(rostring fname);
  ~EmitCode();

  string const &getFname() const { return fname; }

  // get current line number; flushes internally
  int getLine();

  // flush data in stringBuffer to 'os'
  void flush();
};


// return a #line directive for the given location
string lineDirective(SourceLoc loc);  

// emit a #line directive to restore reporting to the
// EmitCode file itself (the 'sb' argument must be an EmitFile object)
stringBuilder &restoreLine(stringBuilder &sb);


#endif // EMITCODE_H
