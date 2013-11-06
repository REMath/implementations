(***********************************)
(* LEGO Summerschool August 1995   *)
(* Hetzelsdorf                     *)
(* Author: Zhaohui Luo             *)
(* Email: Zhaohui.Luo@durham.ac.uk *)
(***********************************)
Module lib_adt_array Import lib_nat lib_adt_basics;

(**********************
***** ADT ARRAY *******
**********************)

(* structure type *)
Record [Str_ARRAY:STR] ElimOver Type
Fields [Array   :Setoid]
       [newarray:Array.dom]
       [assign  :nat->Array.dom->nat->Array.dom]
       [access  :Array.dom->nat->nat];

(* axioms *)
[A:Str_ARRAY];
[EqARRAY  = Equivalence (Setoid_eq|A.Array)];	
[AxARRAY1 = {i:nat}Eq (A.access A.newarray i) zero]; 
[AxARRAY2 = {n,i,j:nat}{arr:A.Array.dom}
		and ((Eq i j) -> 
		     (Eq (A.access (A.assign n arr i) j) n))
		    ((not (Eq i j)) -> 
		     (Eq (A.access (A.assign n arr i) j) (A.access arr j)))
];
[Ax_ARRAY = and3 EqARRAY AxARRAY1 AxARRAY2];
Discharge A;

[ARRAY = make_SPEC Str_ARRAY Ax_ARRAY : SPEC];


