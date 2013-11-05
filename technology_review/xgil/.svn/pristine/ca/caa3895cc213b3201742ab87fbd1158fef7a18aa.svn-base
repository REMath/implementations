#!/bin/sh

# Run this script to build sixgill from SVN
# (Borrowed from the openchange script of similar use)

## insert all possible names (only works with
## autoconf 2.x
TESTAUTOHEADER="autoheader autoheader-2.53 autoheader2.50 autoheader259 autoheader253"
TESTAUTOCONF="autoconf autoconf-2.53 autoconf2.50 autoconf259 autoconf253"
TESTACLOCAL="aclocal aclocal19"

AUTOHEADERFOUND="0"
AUTOCONFFOUND="0"
ACLOCALFOUND="0"

##
## Look for autoheader
##
for i in $TESTAUTOHEADER; do
        if which $i > /dev/null 2>&1; then
                if test `$i --version | head -n 1 | cut -d.  -f 2 | tr -d [:alpha:]` -ge 53; then
                        AUTOHEADER=$i
                        AUTOHEADERFOUND="1"
                        break
                fi
        fi
done

##
## Look for autoconf
##

for i in $TESTAUTOCONF; do
        if which $i > /dev/null 2>&1; then
                if test `$i --version | head -n 1 | cut -d.  -f 2 | tr -d [:alpha:]` -ge 53; then
                        AUTOCONF=$i
                        AUTOCONFFOUND="1"
                        break
                fi
        fi
done

##
## Look for aclocal
##
for i in $TESTACLOCAL; do
        if which $i > /dev/null 2>&1; then
                ACLOCAL=$i              
                ACLOCALFOUND="1"
                break
        fi
done


##
## do we have it?
##
if test "$AUTOCONFFOUND" = "0" -o "$AUTOHEADERFOUND" = "0"; then
        echo "$0: need autoconf 2.53 or later to build openchange from SVN" >&2
        exit 1
fi

if test "$ACLOCALFOUND" = "0"; then
        echo "$0: aclocal not found" >&2
        exit 1
fi


rm -rf autom4te*.cache
rm -f configure include/config.h*

echo "$0: running $ACLOCAL"
$ACLOCAL || exit 1

echo "$0: running $AUTOHEADER"
$AUTOHEADER || exit 1

echo "$0: running $AUTOCONF"
$AUTOCONF || exit 1


rm -rf autom4te*.cache

echo "Now run ./configure and make"
exit 0
