#!/bin/sh

# Install fuzzgrind dependencies  
#  - compile fuzzgrind testcases and fault detection tool
#  - download binary version of STP
#  - download valgrind 3.3.1 sources and compile them

VG_VER=3.4.1


###############################################################################
# Testcases and fault detection tool
###############################################################################

echo '[fuzzgrind] Compiling some binaries'
make -C fault_detection/
make -C testcase/


###############################################################################
# STP
###############################################################################

if [ ! -e stp.tar.gz ]; then
    echo '[fuzzgrind] Downloading STP' 
    wget http://people.csail.mit.edu/vganesh/STP_files/stp.tar.gz
fi

if [ ! -e stp/stp ]; then
    echo '[fuzzgrind] Installing STP into stp/'
    mkdir -p stp/
    tar -C  stp/ -xzf stp.tar.gz
fi


###############################################################################
# Valgrind
###############################################################################

if [ ! -e "valgrind-${VG_VER}.tar.bz2" ]; then
    echo "[fuzzgrind] Downloading valgrind ${VG_VER}" 
    wget http://valgrind.org/downloads/valgrind-${VG_VER}.tar.bz2
fi

if [ ! -e "valgrind-${VG_VER}/README" ]; then
    echo "[fuzzgrind] Extracting valgrind-${VG_VER}.tar.bz2" 
    tar --ignore-failed-read -jkxf "valgrind-${VG_VER}.tar.bz2"
fi

cd "valgrind-${VG_VER}"

if [ ! -e ./fuzzgrind/Makefile ]; then
    echo '[fuzzgrind] Configuring valgrind'
    mkdir -p build/
    ./autogen.sh
    ./configure --prefix=`pwd`/build/
fi

if [ ! -e ./fuzzgrind/fuzzgrind-x86-linux ]; then
    echo '[fuzzgrind] Making valgrind'
    make
fi

if [ ! -e ./build/bin/valgrind ]; then
    echo '[fuzzgrind] Installing valgrind'
    make install
fi
