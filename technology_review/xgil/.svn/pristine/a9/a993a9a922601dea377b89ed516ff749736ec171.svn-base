// cc_ast.h            see license.txt for copyright and terms of use
// a level of indirection for including the generated AST header file

// The idea here is that, since most files are dependent on the AST
// declarations, and it's sometimes useful to globally change which
// set of declarations are in use, this file could be replaced by
// an extension analysis to accomplish that end.  Of course, such a
// change should not then be committed back into the main Elsa CVS
// repository.

// The most obvious alternative mechanism for accomplishing this would
// be to make a preprocessor symbol that expands to "cc.ast.gen.h" by
// default.  However, I (Scott) don't like to mix #defines and
// #includes because it can make it quite difficult to understand
// what happens during preprocessing.

#ifndef CC_AST_H
#define CC_AST_H

#include "cc.ast.gen.h"     // Elsa's name for the C++ AST declarations file

#endif // CC_AST_H
