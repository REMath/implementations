(***********************************)
(* Author: Zhaohui Luo             *)
(* Email: Zhaohui.Luo@durham.ac.uk *)
(***********************************)
Module lib_adt_basics Import lib_sigma lib_setoid;

(****************************************************
***** general structures of specifications/ADTs *****
*****************************************************)

[STR = Type];				(* class of structure types *)

(* class of specifications/ADTs *)
Record [SPEC:Type] ElimOver Type
Fields [Str:STR]
       [Ax: Str->Prop];

[Spec[S:STR]  = S->Prop];			(* class of S-specifications *)
[Model [SP:SPEC]= Sigma SP.Str SP.Ax];          (* model set of SP with proofs *)
[Consistent [SP:SPEC] = Ex [s:SP.Str] SP.Ax s]; (* consistency of a spec *)

(**************************************************************
****** type-theoretic notion of implementation/refinement *****
***************************************************************)

(* A basic notion bt specs with the same str-types *)
[Impl [S|STR][P,P':S.Spec] = {s:S}(P' s)->(P s)];

(* satisfaction condition *)
[Sat [SP,SP'|SPEC][f:SP'.Str->SP.Str] = {s':SP'.Str}(SP'.Ax s')->(SP.Ax (f s'))];

(* type-theoretic notion of implementation *)
Record [IMPL1:Type] ElimOver Type
Parameters [SP,SP'|SPEC]
Fields [refn:SP'.Str->SP.Str]	(* refinement map *)
       [sat :refn.Sat];		(* proof of satisfaction condition *)
Discharge SP;

[IMPL = [SP,SP':SPEC]IMPL1|SP|SP'];



(**********************************************
******** specification/ADT operations *********
***********************************************)

(* 1. Basic operations: Cross, SigmaCirc, Pi, Con, Sel *)
(* 2. Oprns definable from basic ones: Join, Extend, Hide, ... *)

(* Basic spec oprns *)

(* Extend *)
[Extend [SP:SPEC][ext_str:SP.Str->STR]
	[S'=Sigma SP.Str [s:SP.Str]s.ext_str]
	[ext_ax:S'->Prop] 
      = make_SPEC S' [s':S']and (SP.Ax s'.sig_pi1) (ext_ax s')
      : SPEC
];
[Extend_AxOnly [SP:SPEC][ext_ax:SP.Str->Prop] 
      = make_SPEC SP.Str [s:SP.Str]and (SP.Ax s) (ext_ax s)
      : SPEC
];

(* Join *)
[Join [S|STR][SP,SP':S.Spec] 
    = make_SPEC S [s:S]and (SP s) (SP' s)
    : SPEC
];

(* Cross *)
[Cross [SP,SP':SPEC] 
     = [S=Prod SP.Str SP'.Str]
       make_SPEC S [s:S]and (SP.Ax s.sig_pi1) (SP'.Ax s.sig_pi2)
     : SPEC
];

(* SigmaCirc *)
[SigmaCirc [SP:SPEC][P:SP.Str->SPEC]
     = [S=Sigma SP.Str [s:SP.Str](P s).Str]
       make_SPEC S [s:S]and (SP.Ax s.sig_pi1) ((P s.sig_pi1).Ax s.sig_pi2)
     : SPEC
];

(* Pi *)
[Pi [SP:SPEC][P:SP.Str->SPEC]
     = [S={s:SP.Str}(P s).Str]
       make_SPEC S [f:S]{s:SP.Str}(SP.Ax s)->((P s).Ax (f s))
     : SPEC
];

(* Con, constructors --- image constructed *)
[Con [S,S'|STR][k:S'->S][P':S'.Spec] = 
     [s:S] Ex [s':S'] and (P' s') (Eq (k s') s) : S.Spec];

(* Sel, selectors --- inverse image selected *)
[Sel [S,S'|STR][j:S'->S][P:S.Spec] = [s':S'] P (j s') : S'.Spec];

(* Abs, abstractors *)
[Abs [S|STR][R:S->S->Prop][P:S.Spec] =
     [s:S] Ex [s':S] and (P s') (R s s') : S.Spec];


(* Hide, defined just as an arbitrary constructor! *)
(* When the map is forgetful, it hides the forgotten parts of the structure *)
[Hide [S|STR][SP:SPEC][f:SP.Str->S] = make_SPEC S (Con f SP.Ax) : SPEC ];
