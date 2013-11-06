(***********************************)
(* LEGO Summerschool August 1995   *)
(* Hetzelsdorf                     *)
(* Author: Zhaohui Luo             *)
(* Email: Zhaohui.Luo@durham.ac.uk *)
(***********************************)
Module lib_adt_stack Import lib_nat lib_adt_basics; 

(*********************
***** ADT STACK ******
*********************)

[eq = Setoid_eq];

(* structure type *)
Record [Str_STACK:STR] ElimOver Type
Fields [Stack:Setoid]
       [empty:Stack.dom]
       [push :nat->Stack.dom->Stack.dom]
       [pop  :Stack.dom->Stack.dom]
       [top  :Stack.dom->nat];

(* axioms *)
[S:Str_STACK];
[EqSTACK  = Equivalence (eq|S.Stack)]; 	
[AxSTACK1 = eq (S.pop S.empty) S.empty]; 
[AxSTACK2 = Eq (S.top S.empty) zero];  
[AxSTACK3 = {n:nat}{s:S.Stack.dom}eq (S.pop (S.push n s)) s];
[AxSTACK4 = {n:nat}{s:S.Stack.dom}Eq (S.top (S.push n s)) n];

[Ax_STACK = and5 EqSTACK AxSTACK1 AxSTACK2 AxSTACK3 AxSTACK4];
Discharge S;

[STACK = make_SPEC Str_STACK Ax_STACK : SPEC];


