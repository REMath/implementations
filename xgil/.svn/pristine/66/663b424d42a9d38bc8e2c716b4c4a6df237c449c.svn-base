#!/bin/sh
# given some compiler command-line args (including source file),
# output a Makefile line of dependencies for compiling that source file

echo "do not use me" >&2
exit 2

# stolen from http://www.tip.net.au/~millerp/rmch/recu-make-cons-harm.html

# invoke gcc's preprocessor to discover dependencies:
#   -MM   output Makefile rule, ignoring "#include <...>" lines
#         (so as to avoid dependencies on system headers)
# then invoke sed:
#   - remove any occurrences of system headers if they sneak in
gcc -MM "$@" |
  sed -e 's@ /[^ ]*@@g'

# obsolete:
#   - make the .d file itself depend on the same things the .o does
#  -e 's@^\(.*\)\.o:@\1.d \1.o:@'
