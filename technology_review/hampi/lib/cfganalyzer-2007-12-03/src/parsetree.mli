open Cfg ;;

type parsetree = Leaf of string
               | BinNode of string * parsetree * parsetree
               | Node of string * parsetree
	       | Derivation of string * parsetree
	       | AmbDerivation of string * parsetree

val extractParseTree     : fullCFG -> int -> parsetree 
val extractTwoParseTrees : fullCFG -> int -> (parsetree * parsetree option) 

