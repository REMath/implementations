# Makefile for installing Lego.
#
# Edit variables below for your system, if necessary.
#
# David Aspinall <da@dcs.ed.ac.uk>
# June 1998.

INSTALLROOT=/usr/local
# where the shell scripts lego and legoML go
BINDIR=$(INSTALLROOT)/bin
# where the lego library goes
LIBDIR=$(INSTALLROOT)/lib/lego
# where the object binaries for lego and legoML go
OBJDIR=$(LIBDIR)

# Install program
INSTALL=install
# If you don't have -d argument to install, use 'mkdir -p'.
# GNU install gives error if dir already exists, errors are ignored below.
INSTALLDIR=install -d

######################################################################

default: nobuild

install: install-lib install-bin install-scripts


# Note for Edinburgh DCS: 'install' doesn't copy files recursively, so
# we use use cp -pr below.  This breaks the CS_INSTALL substitution,
# so set LIBDIR in /export before doing make install-lib.  End note.
install-lib:
	-$(INSTALLDIR) $(LIBDIR)
	cp -pr lib/* $(LIBDIR)

install-bin:
	-$(INSTALLDIR) $(OBJDIR)
	$(INSTALL) bin/lego   $(OBJDIR)/lego.bin
	$(INSTALL) bin/legoML $(OBJDIR)/legoML.bin

install-scripts:
	-$(INSTALLDIR) $(BINDIR)
	cat lego.sh | sed 's|%LIBDIR%|$(LIBDIR)|g' | sed 's|%OBJ%|$(OBJDIR)/lego.bin|g' > lego
	chmod a+x lego
	$(INSTALL) lego $(BINDIR)
	cat lego.sh | sed 's|%LIBDIR%|$(LIBDIR)|g' | sed 's|%OBJ%|$(OBJDIR)/legoML.bin|g' > legoML
	chmod a+x legoML
	$(INSTALL) legoML $(BINDIR)

nobuild:
	@echo "Type  'make install' to install lego."
	@echo "There is no build: Lego comes with pre-compiled binaries."
	@echo "You can inspect the sources in the src/ and lib/ directories."

