include Makefile.common

VS_BACKSLASH := $(TARGETS:%.vo=%.v)
VS := $(subst \,/,$(VS_BACKSLASH))

default: all

Makefile.coq: GNUmakefile $(VS)
	coq_makefile -I x86 $(VS) -o Makefile.coq

include Makefile.coq
