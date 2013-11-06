open Zchaff ;;
open Basics ;;
open Cfg ;;

(* variable T(a,i) is used to denote that the i-th letter of the word to be found is `a'
   0 <= i < k, a : alphabet *)

(* variable N(A,i,j,m) represents the occurrence of nonterminal A in table entry (i,j) on level m, 
   0 <= i <= j < k, 0 <= m <= 1 *)

(* variable H(B,C,i,j,h) is used as an auxiliary variable to obtain CNF *)

(* variable B(j) is used as an auxiliary variable to encode the constraints for starting nonterminals in
   the intersection and inclusion problem *)


type variable = T of (string * int)      
              | T' of (string * int)      
              | N of (fullCFG * string * int * int)
              | H of (fullCFG * string * string * int * int * int)
              | B of int
              | B' of int
              | Two of (string * int * int)
              | One of (string * int * int)
	      | A of (fullCFG * string * int * int)
	      | AO of (string * int * int * int)
	      | AT of (string * int * int * int)
	      | ATH of (string * string * int * int * int)
	      | AOH of (string * string * int * int * int)
(*
              | H12 of (fullCFG * string * string * int * int * int)
              | H21 of (fullCFG * string * string * int * int * int)
	      | C of (fullCFG * string * int * int)
	      | D of (fullCFG * string * string * string * string * int * int * int * int)
              | H' of (fullCFG * string * string * string * int * int)
*)

let showVar v = match v with 
                      T(a,i) -> "T(" ^ a ^ "," ^ string_of_int i ^ ")"
                    | T'(a,i) -> "T'(" ^ a ^ "," ^ string_of_int i ^ ")"
      		    | N(_,v,i,j) -> "N(" ^ v ^ "," ^ string_of_int i ^ "," ^ string_of_int j ^ ")"
      		    | H(_,b,c,i,j,h) -> "H(" ^ b ^ "," ^ c ^ "," ^ string_of_int i ^ "," ^ string_of_int j ^ "," ^
                                      string_of_int h ^ ")"
      		    | B(i) -> "B(" ^ string_of_int i ^ ")"
      		    | B'(i) -> "B(" ^ string_of_int i ^ ")"
		    | Two(b,j,p) -> "2(" ^ b ^ "," ^ string_of_int j ^ "," ^ string_of_int p ^ ")"
		    | One(b,j,p) -> "1(" ^ b ^ "," ^ string_of_int j ^ "," ^ string_of_int p ^ ")"
		    | A(_,b,j,cnt) -> "A(" ^ b ^ "," ^ string_of_int j ^ "," ^ string_of_int cnt ^ ")"
		    | AO(b,j,cnt,h) -> "AO(" ^ b ^ "," ^ string_of_int j ^ "," ^ string_of_int cnt ^ "," ^ string_of_int h ^ ")"
		    | AT(b,j,cnt,h) -> "AT(" ^ b ^ "," ^ string_of_int j ^ "," ^ string_of_int cnt ^ "," ^ string_of_int h ^ ")"
		    | AOH(b,c,j,cnt,h) -> "AOH(" ^ b ^ "," ^ c ^ "," ^ string_of_int j ^ "," ^ string_of_int cnt ^ "," ^ 
                                          string_of_int h ^ ")"
		    | ATH(b,c,j,cnt,h) -> "ATH(" ^ b ^ "," ^ c ^ "," ^ string_of_int j ^ "," ^ string_of_int cnt ^ "," ^ 
                                          string_of_int h ^ ")"
(*
      		    | H12(_,b,c,i,j,h) -> "H12(" ^ b ^ "," ^ c ^ "," ^ string_of_int i ^ "," ^ string_of_int j ^ "," ^
                                        string_of_int h ^ ")"
      		    | H21(_,b,c,i,j,h) -> "H21(" ^ b ^ "," ^ c ^ "," ^ string_of_int i ^ "," ^ string_of_int j ^ "," ^
                                        string_of_int h ^ ")"
		    | C(_,a,i,j) -> "C(" ^ a ^ "," ^ string_of_int i ^ "," ^ string_of_int j ^ ")"
		    | D(_,b,c,b',c',i,j,h,h') -> "D(" ^ b ^ "," ^ c ^ "," ^ b' ^ "," ^ c' ^ "," ^ string_of_int i ^ 
                                               "," ^ string_of_int j ^ "," ^ string_of_int h ^ "," ^ 
                                               string_of_int h' ^ ")"
      		    | H'(_,a,b,c,i,j) -> "H'(" ^ a ^ "," ^ b ^ "," ^ c ^ "," ^ string_of_int i ^ "," ^ string_of_int j 
                                         ^ ")"
*)

let showPosVar = showVar
let showNegVar v = "-" ^ (showVar v)


exception Invalid_code of int

module HashVariable =
struct
  type t = variable

  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end ;;


module VarTable = Hashtbl.Make(HashVariable) ;;

let table = VarTable.create 1000


let getCode var = try
                    VarTable.find table var
                  with Not_found -> (-1)

let encode var = try 
                   VarTable.find table var
                 with Not_found -> (let n = zchaff_AddVariable zchaff in
                                    VarTable.add table var n;
                                    n)

let posEncode = encode
let negEncode var = -(encode var)

(* exception Variable_unknown_to_zchaff of string *)

let getValue v = let c = getCode v in
                 (* if 0 < c && c <= zchaff_NumVariables zchaff
                 then *) zchaff_GetVarAsgnment zchaff c
                 (* else raise(Variable_unknown_to_zchaff(showVar v)) *)

let showAllValues _ =
  message 3 (fun _ -> "Showing current variable assignment:\n");
  VarTable.iter
    (fun v -> fun c -> message 3 (fun _ -> "  " ^ string_of_int c ^ ": " ^ showVar v ^ " = " ^ 
                                  string_of_int(getValue(v)) ^ "\n"))
    table
