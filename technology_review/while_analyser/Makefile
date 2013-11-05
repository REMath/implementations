LIBPATH =
OCAMLOPT=ocamlopt -dtypes $(LIBPATH)
OCAMLC=ocamlc -g -dtypes $(LIBPATH)
LIBS=nums

SRCML= syntax.ml print.ml while_parser.ml while_lexer.ml parse.ml \
       cfg.ml envLattice.ml analyse.ml \
       envAbstractionNotRelational.ml \
       numAbstractionSign.ml numAbstractionInterval.ml \
       main.ml
SRCMLI= syntax.mli print.mli parse.mli cfg.mli lattice.mli \
		abstraction.mli envLattice.mli analyse.mli \
		envAbstractionNotRelational.mli \
		numAbstractionSign.mli numAbstractionInterval.mli main.mli

analyse : all
	@echo "[ocamlc -o analyse] "
	@$(OCAMLC) -o analyse $(LIBS:=.cma) $(SRCML:.ml=.cmo)

all: $(SRCMLI:.mli=.cmi) $(SRCML:.ml=.cmo)

while_lexer.ml :while_lexer.mll while_parser.cmi
	@echo "[ocamllex ] "$<
	@ocamllex -q $<
while_parser.ml while_parser.mli : while_parser.mly
	@echo "[ocamlyacc] "$<
	@ocamlyacc $<
while_parser.cmo : while_parser.cmi
while_parser.cmi : while_parser.mli syntax.cmo

doc: all
	ocamldoc $(SRCMLI) -d doc -html -sort

.PHONY: doc depend

.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	@echo "[ocamlc -c] "$<
	@$(OCAMLC) -c $<
.mli.cmi:
	@echo "[ocamlc -c] "$<
	@$(OCAMLC) -c $<
.ml.cmx:
	@echo "[ocamlopt] "$<
	@$(OCAMLOPT) -c $<

distrib: clean
	cd ..;	mkdir while_analyser; cp -r caml/* while_analyser/;	tar -czf caml/while_analyser.tgz while_analyser; rm -fr ../while_analyser

clean::
	rm -f *.cm[iox] *.o *~ *.annot while_lexer.ml while_parser.ml while_parser.mli analyse doc/*.html example/*~ while_analyser.tgz

depend:
	ocamldep $(LIBPATH) $(SRCML) analyse.mli while_parser.mli $(SRCMLI) > .depend

-include .depend