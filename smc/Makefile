
all: Makefile.coq
	make -f Makefile.coq html COQDOCFLAGS='-utf8 -g'

Makefile.coq:
	coq_makefile -f _CoqProject -o $@

clean:
	make -f Makefile.coq clean

ext-clean: clean
	rm -f extraction/*.ml extraction/*.mli

