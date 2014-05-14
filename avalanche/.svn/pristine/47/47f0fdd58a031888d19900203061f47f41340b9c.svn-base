#!/bin/sh -x

set -ex
aclocal
autoheader
automake --add-missing --copy --foreign
autoconf

(cd valgrind; ./autogen.sh)
(cd stp-ver-0.1-11-18-2008; ./autogen.sh)
