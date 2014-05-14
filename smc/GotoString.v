Require Import
  Utf8 String
  Integers
  PrintPos
  Goto.

Local Open Scope string_scope.

Definition string_of_reg (r: register) : string :=
  match r with
  | R0 => "R0"
  | R1 => "R1"
  | R2 => "R2"
  | R3 => "R3"
  | R4 => "R4"
  | R5 => "R5"
  | R6 => "R6"
  | R7 => "R7"
  end.

Definition string_of_int (i: int) : string :=
  string_of_z (Int.signed i).
