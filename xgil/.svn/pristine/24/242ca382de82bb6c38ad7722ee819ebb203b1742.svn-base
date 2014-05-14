
# Sixgill: Static assertion checker for C/C++ programs.
# Copyright (C) 2009-2010  Stanford University
# Author: Brian Hackett
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# this file includes the results of the autoconf run
include config.mk

# configure --enable-debug
ifdef DEBUG
  OPT = -O0 -DDEBUG
else
  OPT = -O2
endif

WARNINGS = -Wall -Wno-non-virtual-dtor -Wno-delete-non-virtual-dtor -Wno-strict-aliasing -Werror
CPPFLAGS = -g ${OPT} -I${PWD} ${HOST_CFLAGS} ${WARNINGS}
LDFLAGS = ${HOST_LDFLAGS} -lz -lgmp ${EXTRA_LDFLAGS}

# run 'make profile' to enable profiling in generated binaries
ifdef PROFILE
  CPPFLAGS += -pg
  LDFLAGS += -pg
endif

BACKEND_INC = \
	backend/action.h \
	backend/backend.h \
	backend/backend_block.h \
	backend/backend_compound.h \
	backend/backend_hash.h \
	backend/backend_util.h \
	backend/backend_xdb.h \
	backend/operand.h \
	backend/serial.h \
	backend/transaction.h

IMLANG_INC = \
	imlang/bit.h \
	imlang/block.h \
	imlang/exp.h \
	imlang/filename.h \
	imlang/interface.h \
	imlang/loopsplit.h \
	imlang/opcode.h \
	imlang/serial.h \
	imlang/storage.h \
	imlang/trace.h \
	imlang/type.h \
	imlang/variable.h \
	imlang/visitor.h

MEMORY_INC = \
	memory/alias.h \
	memory/baked.h \
	memory/mblock.h \
	memory/callgraph.h \
	memory/clobber.h \
	memory/escape.h \
	memory/modset.h \
	memory/serial.h \
	memory/simplify.h \
	memory/mstorage.h \
	memory/summary.h

INFER_INC = \
	infer/expand.h \
	infer/infer.h \
	infer/invariant.h \
	infer/nullterm.h

CHECK_INC = \
	check/checker.h \
	check/decision.h \
	check/frame.h \
	check/path.h \
	check/propagate.h \
	check/sufficient.h \
	check/where.h

SOLVE_INC = \
	solve/constraint.h \
	solve/solver.h \
	solve/solver_hash.h \
	solve/solver-mux.h \
	solve/union_find.h

UTIL_INC = \
	util/alloc.h \
	util/assert.h \
	util/buffer.h \
	util/config.h \
	util/hashcache.h \
	util/hashcache_impl.h \
	util/hashcons.h \
	util/hashcons_impl.h \
	util/hashtable.h \
	util/hashtable_impl.h \
	util/list.h \
	util/monitor.h \
	util/primitive.h \
	util/stream.h \
	util/istream.h \
	util/ostream.h \
	util/timer.h \
	util/vector.h \
	util/xml.h

XDB_INC = \
	xdb/layout.h \
	xdb/xdb.h

INCLUDE = \
	${BACKEND_INC} \
	${IMLANG_INC} \
	${MEMORY_INC} \
	${INFER_INC} \
	${CHECK_INC} \
	${SOLVE_INC} \
	${UTIL_INC} \
	${XDB_INC}

BACKEND_OBJS = \
	backend/action.o \
	backend/backend.o \
	backend/backend_block.o \
	backend/backend_compound.o \
	backend/backend_hash.o \
	backend/backend_util.o \
	backend/backend_xdb.o \
	backend/operand.o \
	backend/transaction.o

IMLANG_OBJS = \
	imlang/bit.o \
	imlang/block.o \
	imlang/exp.o \
	imlang/filename.o \
	imlang/interface.o \
	imlang/loopsplit.o \
	imlang/opcode.o \
	imlang/storage.o \
	imlang/trace.o \
	imlang/type.o \
	imlang/variable.o

MEMORY_OBJS = \
	memory/alias.o \
	memory/baked.o \
	memory/mblock.o \
	memory/callgraph.o \
	memory/clobber.o \
	memory/escape.o \
	memory/modset.o \
	memory/simplify.o \
	memory/mstorage.o \
	memory/summary.o

INFER_OBJS = \
	infer/expand.o \
	infer/infer.o \
	infer/invariant.o \
	infer/nullterm.o

CHECK_OBJS = \
	check/checker.o \
	check/decision.o \
	check/frame.o \
	check/path.o \
	check/propagate.o \
	check/sufficient.o \
	check/where.o

SOLVE_OBJS = \
	solve/constraint.o \
	solve/solver.o \
	solve/solver-mux.o \
	solve/union_find.o

UTIL_OBJS = \
	util/alloc.o \
	util/assert.o \
	util/buffer.o \
	util/config.o \
	util/hashcons.o \
	util/json.o \
	util/monitor.o \
	util/primitive.o \
	util/stream.o \
	util/timer.o \
	util/xml.o

XDB_OBJS = \
	xdb/layout.o \
	xdb/xdb.o

LIB_OBJS = \
	${BACKEND_OBJS} \
	${IMLANG_OBJS} \
	${MEMORY_OBJS} \
	${UTIL_OBJS} \
	${XDB_OBJS}

XDB_LIB_OBJS = \
	util/buffer.o \
	util/json.o \
	${XDB_OBJS} \
	xdb/library.o

CHK_OBJS = \
	${INFER_OBJS} \
	${CHECK_OBJS} \
	${SOLVE_OBJS}

ALL_LIBS = \
	bin/libxcheck.a \
	bin/libxgill.a

ALL_BINS = \
	bin/xcheck \
	bin/xinfer \
	bin/xmemlocal \
	bin/xsource \
	bin/xdbfind \
	bin/xdbkeys \
	bin/xmanager \
	bin/xdb.so

# additional settings for Yices.
ifeq ($(USE_YICES),yes)
CPPFLAGS += -DSOLVER_YICES=1 -I${YICES_DIR}/include
INCLUDE += solve/solver-yices.h solve/wrapyices.h
CHK_OBJS += solve/solver-yices.o solve/wrapyices.o
ALL_LIBS += ${YICES_DIR}/lib/libyices.a
.have_yices: ${YICES_DIR}/lib/libyices.a ${YICES_DIR}/include/yices_c.h
else
.have_yices:
endif

# additional settings for CVC3.
ifeq ($(USE_CVC3),yes)
CPPFLAGS += -DSOLVER_CVC3=1 ${CVC3_CFLAGS}
INCLUDE += solve/solver-cvc3.h solve/cvc3_interface.h
CHK_OBJS += solve/solver-cvc3.o solve/cvc3_interface.o
endif

%.o: %.cpp ${INCLUDE}
	${CXX} ${CPPFLAGS} -fPIC -c $< -o $@

all: .have_yices build-libevent ${ALL_LIBS} ${ALL_BINS} build-plugin # build-elsa

profile:
	$(MAKE) all "PROFILE=1"

bin/xdb.so: ${XDB_LIB_OBJS}
	rm -f $@
	${CXX} -shared -fPIC -o $@ ${XDB_LIB_OBJS} -lz ${EXTRA_LDFLAGS}

bin/libxgill.a: ${LIB_OBJS}
	rm -f $@
	ar -r $@ ${LIB_OBJS}

bin/libxcheck.a: ${CHK_OBJS}
	rm -f $@
	ar -r $@ ${CHK_OBJS}

ifeq ($(GCC_PLUGIN_SUPPORT),yes)
build-plugin:
	make -C gcc
else
build-plugin:
endif

BUILD_LIBS = ${ALL_LIBS} ${CVC3_LIBS} ${LDFLAGS}

bin/xdbfind: main/xdbfind.o ${ALL_LIBS}
	${CXX} $< -o $@ ${BUILD_LIBS}

bin/xdbkeys: main/xdbkeys.o ${ALL_LIBS}
	${CXX} $< -o $@ ${BUILD_LIBS}

bin/xsource: main/xsource.o ${ALL_LIBS}
	${CXX} $< -o $@ ${BUILD_LIBS}

bin/xmemlocal: main/xmemlocal.o ${ALL_LIBS}
	${CXX} $< -o $@ ${BUILD_LIBS}

bin/xbrowse: main/xbrowse.o ${ALL_LIBS}
	${CXX} $< -o $@ ${BUILD_LIBS}

bin/xinfer: main/xinfer.o ${ALL_LIBS}
	${CXX} $< -o $@ ${BUILD_LIBS}

bin/xcheck: main/xcheck.o ${ALL_LIBS}
	${CXX} $< -o $@ ${BUILD_LIBS}

bin/xmanager: main/xmanager.o ${ALL_LIBS}
	${CXX} libevent/*.o $< -o $@ ${BUILD_LIBS}

# libevent stuff

build-libevent: libevent/Makefile
	make -C libevent

libevent/Makefile:
	cd libevent && ./configure

# Elsa frontend stuff

ifdef DEBUG

build-elsa:
	make -C elsa debug

else # DEBUG

build-elsa:
	make -C elsa

endif # DEBUG

# other

clean:
	rm -f ${LIB_OBJS} ${CHK_OBJS} bin/libmemory.a bin/libimlang.a bin/libxgill.a bin/libxcheck.a ${ALL_BINS} main/*.o
	rm -f config.log config.status
	make -C gcc clean
	make -C libevent clean

distclean: clean
	rm -f config.mk config.h
	make -C libevent distclean
