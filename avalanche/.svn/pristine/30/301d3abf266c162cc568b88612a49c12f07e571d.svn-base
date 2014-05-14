pkglibdir = $(libdir)/avalanche
pkglib_PROGRAMS = stp

INCLUDES = -I../sat/mtl -I../sat/core -I../sat/simp
YFLAGS = -d -v

CXXLD = $(CC)
LIBS = -static-libgcc -Wl,-Bstatic,-lstdc++,-Bdynamic -lm

stp_LDADD = -L../AST -last -L../sat/core -lminisat \
	    -L../simplifier -lsimplifier -L../bitvec -lconsteval \
	    -L../constantbv -lconstantbv

stp_SOURCES = lexPL.cpp parsePL.cpp let-funcs.cpp main.cpp
dist_noinst_DATA = PL.lex PL.y

lexPL.cpp: PL.lex parsePL_defs.h
	$(LEX) PL.lex
	mv -f lex.yy.c lexPL.cpp

parsePL.cpp parsePL_defs.h: PL.y
	$(YACC) $(YFLAGS) PL.y
	mv -f y.tab.c parsePL.cpp
	mv -f y.tab.h parsePL_defs.h
