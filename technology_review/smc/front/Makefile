OCB:=ocamlbuild

all: main.native

main.native: Camlcoq.ml main.ml utils.ml parser.mly lexer.mll reloc.ml
	$(OCB) $@

decode.native: decode.ml
	$(OCB) $@

clean:
	$(OCB) -clean
