open Cfg ;;
open Basics ;;

type constraintMaker = int -> int -> constraints

type formalParameter = UpperBound
                     | LowerBound
                     | Null

type problem = { permanent : constraintMaker list;
                 temporary : constraintMaker list;
                 negativeReport : int -> int -> string;
                 positiveReport : int -> int -> string
               }

val dummyProblem   : fullCFG list -> problem
val emptiness      : fullCFG list -> problem 
val universality   : fullCFG list -> problem
val inclusion      : fullCFG list -> problem
val intersection   : fullCFG list -> problem
val equivalence    : fullCFG list -> problem
val ambiguity      : fullCFG list -> problem

