open Cfg ;;
open Varencoding ;;

type cyktable = variable list array array
type wordtable = variable list array

val makeWordTable : fullCFG -> int -> wordtable
(* val makeCYKTable  : fullCFG -> int -> cyktable *)
