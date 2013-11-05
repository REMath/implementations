
all: ../../bin/ccxgill

debug:
	$(MAKE) all "DEBUG=1"

# directories of other software
SMBASE   := ../smbase
AST      := ../ast
ELKHOUND := ../elkhound
ELSA     := ../elsa
XGILL    := ../..

# stuff inside those other directories
LIBSMBASE   := $(SMBASE)/libsmbase.a
LIBAST      := $(AST)/libast.a
LIBELKHOUND := $(ELKHOUND)/libelkhound.a
LIBELSA     := $(ELSA)/libelsa.a

# yices is only needed for testing scalar simplifications
LIBXGILL    := $(XGILL)/yices/lib/libyices.a \
               $(XGILL)/bin/libmemory.a \
               $(XGILL)/bin/libimlang.a

CXX := g++

ifdef DEBUG
  OPT := -O0 -DDEBUG
else
  OPT := -O2 -DNDEBUG
endif

# flags for the C++ compiler (and preprocessor)
CCFLAGS := -g -Wall -Wno-non-virtual-dtor -Wno-deprecated -D__UNIX__ $(OPT) -DNDEBUG -D__LINUX__ -DXML -Woverloaded-virtual -I$(SMBASE) -I$(AST) -I$(ELKHOUND) -I$(ELSA) -I$(XGILL)

# flags for the linker
libraries := $(LIBELSA) $(LIBELKHOUND) $(LIBAST) $(LIBSMBASE) $(LIBXGILL)
LDFLAGS := -g -Wall $(libraries) -lz -lgmp

IMLANG_OBJS = \
	xgill.o \
	xgill_file.o \
	xgill_expr.o \
	xgill_stmt.o \
	main.o

IMLANG_INCLUDE = \
	xgill.h \
	xgill_file.h

# compile .cc in this directory to a .o
%.o: %.cc $(IMLANG_INCLUDE) $(LIBXGILL)
	$(CXX) -c -o $@ $< $(CCFLAGS)

# compile output binary
../../bin/ccxgill: $(IMLANG_OBJS) $(libraries)
	$(CXX) -o $@ $(IMLANG_OBJS) $(LDFLAGS)

# clean output files
clean:
	rm -f $(IMLANG_OBJS)
