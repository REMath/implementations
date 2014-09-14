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
`ocamlc -c Hf.mli Hf.ml Gen.mli Gen.ml Main.ml`
`ocamlc unix.cma Data.cmo Util.cmo Lexer.cmo Parser.cmo Hf.cmo Gen.cmo Main.cmo -o hf.bin`
rm *.cmo *.cmi
