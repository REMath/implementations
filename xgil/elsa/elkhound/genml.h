// genml.h            see license.txt for copyright and terms of use
// extension to gramanl module that generates ML instead of C

#ifndef GENML_H
#define GENML_H

#include "str.h"      // rostring

class GrammarAnalysis;

// entry point
void emitMLActionCode(GrammarAnalysis const &g, rostring mliFname,
                      rostring mlFname, rostring srcFname);

#endif // GENML_H
