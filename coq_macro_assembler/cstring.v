(*===========================================================================
  C-style zero-terminated strings
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype Ascii String.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Fixpoint containsZero (s: string) := 
  if s is String c s  
  then if Ascii.nat_of_ascii c is 0 then true else containsZero s
  else false.

Structure cstring := CString {
  tval :> string; 
  _ : ~~containsZero tval
}.

Canonical cstring_subType := Eval hnf in [subType for tval].

Canonical emptyString := CString (isT: ~~containsZero ""%string). 

(* Need explicit term really *)
Definition mk_cstring (s: string) : cstring.
case E: (containsZero s). 
exact emptyString.
refine (@CString s _). 
by rewrite E. 
Defined.

Coercion mk_cstring : string >-> cstring. 

Definition consCS (c: ascii) (s: cstring) : cstring.
case E: (Ascii.nat_of_ascii c) => [| n].  
exact s. 
refine (@CString (String c s) _).
simpl. rewrite E. by destruct s. 
Defined. 

