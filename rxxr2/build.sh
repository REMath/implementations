# © Copyright University of Birmingham, UK

#!/bin/bash
set -e
ocamlyacc RegexParser.mly
ocamllex RegexLexer.mll
ocamlyacc PatternParser.mly
ocamllex PatternLexer.mll
ocamlc -c ParsingData.mli ParsingData.ml
ocamlc -c RegexParser.mli RegexParser.ml
ocamlc -c RegexLexer.ml
ocamlc -c PatternParser.mli PatternParser.ml
ocamlc -c PatternLexer.ml
ocamlc -c ParsingMain.mli ParsingMain.ml
ocamlc -c Common.mli Common.ml
ocamlc -c Nfa.mli Nfa.ml
ocamlc -c RegexScanner.mli RegexScanner.ml
ocamlc -c Flags.mli Flags.ml
ocamlc -c Word.mli Word.ml
ocamlc -c Util.mli Util.ml
ocamlc -c Beta.mli Beta.ml
ocamlc -c Phi.mli Phi.ml
ocamlc -c Triple.mli Triple.ml
ocamlc -c Product.mli Product.ml
ocamlc -c XAnalyser.mli XAnalyser.ml
ocamlc -c Y1Analyser.mli Y1Analyser.ml
ocamlc -c Y2Analyser.mli Y2Analyser.ml
ocamlc -c ZAnalyser.mli ZAnalyser.ml
ocamlc -c AnalyserMain.mli AnalyserMain.ml
ocamlc -c RuleScanner.mli RuleScanner.ml
ocamlc -c Run.ml
ocamlc str.cma ParsingData.cmo RegexParser.cmo RegexLexer.cmo PatternParser.cmo PatternLexer.cmo ParsingMain.cmo Common.cmo Nfa.cmo RegexScanner.cmo Flags.cmo Word.cmo Util.cmo Beta.cmo Phi.cmo Triple.cmo Product.cmo XAnalyser.cmo Y1Analyser.cmo Y2Analyser.cmo ZAnalyser.cmo unix.cma AnalyserMain.cmo RuleScanner.cmo Run.cmo -o scan.bin
rm *.cmi *.cmo RegexParser.mli RegexParser.ml RegexLexer.ml PatternParser.mli PatternParser.ml PatternLexer.ml
