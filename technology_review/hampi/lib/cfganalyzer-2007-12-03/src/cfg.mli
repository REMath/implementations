open Basics ;;

type symbol = Nonterminal of string
            | Terminal of string

type pureCFG = (string * (symbol list list)) list

type alphabet = string list

type fullCFG = { cfg: pureCFG;
                 origcfg: pureCFG;
                 alphabet: string list;
                 nonterminals: string list;
                 start: string;
(*                 termprods: (string * (string list)) list; *)
                 nullable: StringSet.t;
                 ambnullable: StringIntSet.t;
                 ambnonterminals: StringSet.t;
                 ambproductions: StringStringSet.t (*;
                 closure: StringSet.t StringMap.t;
                 ambclosure: StringIntSet.t StringMap.t *)
               }

val showPureCFG : pureCFG -> string

val makeFullCFG : pureCFG -> fullCFG
 
val size : pureCFG -> int * int * int * int * int * int * int

val showUnitProdClosure    : StringSet.t StringMap.t -> string 
val showAmbUnitProdClosure : StringIntSet.t StringMap.t -> string

val number_of_productions : fullCFG -> string -> int
