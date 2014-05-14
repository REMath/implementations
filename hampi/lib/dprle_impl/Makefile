export OCAMLMAKEFILE = ./OCamlMakefile

define PROJ_main
  SOURCES = hashset.ml nfa.ml depgraph.ml solve.ml parse.mly lex.mll dprle.ml
  RESULT = dprle
endef
export PROJ_main

ifndef SUBPROJS
  export SUBPROJS = main
endif

export LIBS =
export INCDIRS =
export PACKS = #unix str
export OCAMLFLAGS =

# Default target to use (dc for debugging, nc for native, pnc for profiling)
all:	nc 

# Catch-all target will be applied to all subprojects automatically
%:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=$@



