(*===========================================================================
    General encoder class, with instances for BYTE and DWORD
  ===========================================================================*)
Require Import ssreflect seq.
Require Import bitsrep update.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Class Encoder X := encode: X -> seq BYTE.

(* The basic encoders for bytes and DWORDs *)
Instance encodeBYTE : Encoder BYTE := fun b => [::b]. 
Instance encodeDWORD : Encoder DWORD := fun d =>
    let: (b3,b2,b1,b0) := split4 8 8 8 8 d in
    encode b0 ++
    encode b1 ++
    encode b2 ++
    encode b3.

Instance encodeWORD : Encoder WORD := fun w =>
    let: (b1,b0) := split2 8 8 w in
    encode b0 ++
    encode b1.

