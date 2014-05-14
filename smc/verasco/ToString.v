Require Import Utf8 String.
Require Import Coqlib Integers.
Require Import PrintPos.
Require Import LatticeSignatures.

Local Open Scope string_scope.

Class ToString A := to_string : A → string.
Instance UnitToString : ToString unit := λ _, "()".
Instance BoolToString : ToString bool := (λ b, if b then "true" else "false").
Instance PosToString : ToString positive := print_pos.
Instance SIntToString : ToString int := string_of_z ∘ Int.signed.
Instance SInt64ToString : ToString int64 := string_of_z ∘ Int64.signed.
Instance ZToString : ToString Z := string_of_z.

Instance ListToString {A} `{ToString A} : ToString (list A) :=
  (λ l, List.fold_left (λ s a, s ++ to_string a ++ "; ") l "[" ++ "]").

Instance PairToString A B `{ToString A} `{ToString B} : ToString (A * B) := λ ab, let '(a, b) := ab in "(" ++ to_string a ++ ", " ++ to_string b ++ ")".

Definition new_line : string := "
".
