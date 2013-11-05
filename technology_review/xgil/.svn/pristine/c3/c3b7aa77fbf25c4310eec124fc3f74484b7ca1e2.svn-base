# Makefile

#tmp: lexer.cmo

all: tobjpool main main.opt

# directories
ELKHOUND := ..

# compiler options
OCAMLCFLAGS := -noassert
#OCAMLCFLAGS :=

#OCAMLOPTFLAGS := $(OCAMLCFLAGS) -p
OCAMLOPTFLAGS := $(OCAMLCFLAGS)

# using dependency strategy from 
# http://www.cs.berkeley.edu/~smcpeak/autodepend/autodepend.html
%.cmo: %.ml
	ocamlc -c -g $(OCAMLCFLAGS) $*.ml
	@ocamldep $*.ml > $*.d

# I'll try maintaining separate dependency info for .cmo and .cmx
%.cmx: %.ml
	ocamlopt -c $(OCAMLOPTFLAGS) $*.ml
	@ocamldep $*.ml > $*.dx

# run elkhound on a grammar spec
# (for now I don't want to use the interface stuff)
# 
# cygwin bug...
#%.ml: %.gr $(ELKHOUND)/elkhound
%.ml: %.gr
	$(ELKHOUND)/elkhound -ocaml -v $*.gr
	rm -f $*.mli

# run ocamllex on a lex spec
%.ml: %.mll
	ocamllex $*.mll

# run ocamlyacc on a parser spec
%.ml: %.mly
	ocamlyacc $*.mly
	rm -f $*.mli

# NOTE: Module order is important!  OCaml module dependencies cannot
# be cyclic, and the order presented must respect the dependency order.

# test program for objpool module
TOBJPOOL_MODULES = \
  arraystack.cmo \
  objpool.cmo \
  tobjpool.cmo
tobjpool: $(TOBJPOOL_MODULES)
	ocamlc -o $@ -g $^

tobjpool.opt: $(TOBJPOOL_MODULES:.cmo=.cmx)
	ocamlopt $(OCAMLOPTFLAGS) -o $@ $^

# these are the minimal set of modules needed for an elkhound parser
MINIMAL_MODULES = \
  smutil.cmo \
  useract.cmo \
  lexerint.cmo \
  parsetables.cmo \
  arraystack.cmo \
  objpool.cmo \
  glr.cmo

# these are modules for the test program; they include some specific 
# grammar tables/actions, a lexer, a deterministic LR parser, the
# parse-tree-printing stuff (ptreenode, ptreeact), and a main() function
MAIN_MODULES = \
  $(MINIMAL_MODULES) \
  arith.cmo \
  een.cmo \
  lrparse.cmo \
  ptreenode.cmo \
  ptreeact.cmo \
  lexer.cmo \
  oc_arith.cmo \
  main.cmo
main: $(MAIN_MODULES)
	ocamlc -o $@ -g $^

main.opt: $(MAIN_MODULES:.cmo=.cmx)
	ocamlopt $(OCAMLOPTFLAGS) -o $@ $^

# dependencies
ALL_MODULES = \
  $(MAIN_MODULES) \
  tobjpool.cmo
-include $(ALL_MODULES:.cmo=.d)
-include $(ALL_MODULES:.cmo=.dx)

# run it a bunch of ways
check:
	echo "2+3" | ./main arith lr
	echo "2+3" | ./main arith glr
	echo "2+3" | ./main een glr
	echo "2+3+4" | ./main een glr ptree
	@echo ""
	@echo Tests PASSED

clean:
	rm -f *.cmo *.cmi *.d *.cmx *.dx
	rm -f arith.ml* een.ml* lexer.ml main tobjpool
