OCAMLOPT=ocamlopt
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex
OCAMLDEP=ocamldep

SED=sed
VERBOSE = 1
#######
# change this to your C++ compiler
# !!! must be the same that was used to compile libsat.a !!!
#######
CPP=g++

OBJDIR=obj
SRCDIR=src
ZCHAFFDIR=zchaff
SUBDIRS=zchaff-src

#######
# change this to the OCaml installation directory
#######
#OCAML_DIR=/users/lange/lib/ocaml
OCAML_DIR=/usr/lib/ocaml

#######
# change this to the directory in which libsat.a is installed
#######
ZCHAFF_INST_DIR=..
ZCHAFF_LIB=$(ZCHAFF_INST_DIR)/libsat.a

INCLUDES=-I $(SRCDIR) \
         -I $(OBJDIR) \
         -I $(ZCHAFFDIR) \
         -I $(OCAML_DIR) \
#        -I $(OCAML_EXTLIB_DIR)


OCAML_ZCHAFF_OBJ_PATH=$(OBJDIR)
OCAML_ZCHAFF_OBJS=$(OCAML_ZCHAFF_OBJ_PATH)/zchaff_ocaml_wrapper.o

MODULES=obj/zchaff.cmx \
        obj/basics.cmx \
        obj/cfg.cmx \
        obj/parser.cmx \
        obj/lexer.cmx \
        obj/varencoding.cmx \
        obj/coding.cmx \
        obj/dotty.cmx \
        obj/problems.cmx \
        obj/engine.cmx

#	obj/cyktable.cmx \
#	obj/latex.cmx \
#	obj/parsetree.cmx \

INTERFACES=$(MODULES:.cmx=.cmi)

EXECUTABLE=bin/cfganalyzer


$(SOURCES:.ml=.cmx:src=obj)

.PHONY : $(SUBDIRS)

all: $(SUBDIRS) $(INTERFACES) $(MODULES) obj/main.cmx $(OCAML_ZCHAFF_OBJS) exec
	@echo "CFGAnalyzer built"

src/parser.ml: src/parser.mly
	$(OCAMLYACC) src/parser.mly

obj/parser.cmi: src/parser.mli
	$(OCAMLOPT) $(INCLUDES) -c -o obj/parser.cmi src/parser.mli

src/lexer.ml: src/lexer.mll
	$(OCAMLLEX) src/lexer.mll

exec:
	$(OCAMLOPT) -o $(EXECUTABLE) -cc $(CPP) $(OCAML_ZCHAFF_OBJS) $(ZCHAFF_LIB) $(MODULES) obj/main.cmx

zchaff-src:
	$(MAKE) -C zchaff-src all
	mv zchaff-src/libsat.a $(ZCHAFF_INST_DIR)

obj/%.cmx: src/%.ml
	$(OCAMLOPT) $(INCLUDES) -c -o $@ $<

obj/%.cmi: src/%.mli
	$(OCAMLOPT) $(INCLUDES) -c -o $@ $<

obj/zchaff_ocaml_wrapper.o:
	$(CPP) -c -g $(INCLUDES) -I $(OCAML_DIR) -o $@ zchaff/zchaff_ocaml_wrapper.cpp

#src/%.mli: src/%.ml
#	$(OCAMLOPT) $(INCLUDES) -i $< > $@

src/lexer.mli: src/lexer.ml
	$(OCAMLOPT) $(INCLUDES) -i src/lexer.ml > src/lexer.mli

src/parser.mli: src/parser.ml
	$(OCAMLOPT) $(INCLUDES) -i src/parser.ml > src/parser.mli

src/basics.mli: src/basics.ml
	$(OCAMLOPT) $(INCLUDES) -i src/basics.ml > src/basics.mli

src/zchaff.mli: src/zchaff.ml
	$(OCAMLOPT) $(INCLUDES) -i src/zchaff.ml > src/zchaff.mli

obj/%.cmi: src/%.mli
	$(OCAMLOPT) $(INCLUDES) -c -o $@ $<

clean:
	rm -f obj/*.o obj/*.cmx obj/*.cmi
	rm -f src/parser.ml src/parser.mli src/lexer.ml src/lexer.mli src/zchaff.mli src/basics.mli
	rm -f $(EXECUTABLE)
	$(MAKE) -C zchaff-src clean

depend:
	$(OCAMLDEP) -native $(INCLUDES) src/*.mli src/*.ml | $(SED) "s/src/obj/g" > .depend


include .depend
