#***********************************************************
#                                                          *
# RXXR - Regular eXpression eXponential Runtime analyser   *
#                                                          *
# Copyright (C) 2012 University of Birmingham              *
#                                                          *
# All rights reserved.                                     *
#                                                          *
# For license conditions, see the file LICENSE.rtf.        *
#                                                          *
#***********************************************************

#!/bin/bash

cdir=`pwd`
commons="$cdir/../common"
cd $commons
`ocamlc -c Data.mli Data.ml Util.mli Util.ml Lexer.mli Lexer.ml Parser.mli Parser.ml`
mv *.cmo *.cmi $cdir
cd $cdir
`ocamlc -c Pwf.mli Pwf.ml Main.ml`
`ocamlc Data.cmo Util.cmo Lexer.cmo Parser.cmo Pwf.cmo Main.cmo -o pwf.bin`
rm *.cmo *.cmi
