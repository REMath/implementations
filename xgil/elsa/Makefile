# Makefile for toplevel elsa distribution

# just do the obvious recursive thing

all: make-flex
	$(MAKE) -C smbase
	$(MAKE) -C ast
	$(MAKE) -C elkhound
	$(MAKE) -C elsa
	$(MAKE) -C imlang

make-flex: flex/Makefile
	$(MAKE) -C flex

flex/Makefile:
	@cd flex && ./configure

debug:
	$(MAKE) -C smbase debug
	$(MAKE) -C ast debug
	$(MAKE) -C elkhound debug
	$(MAKE) -C elsa debug
	$(MAKE) -C imlang debug

clean:
	$(MAKE) -C smbase clean
	$(MAKE) -C ast clean
	$(MAKE) -C elkhound clean
	$(MAKE) -C elsa clean
	$(MAKE) -C imlang clean
