
Require Import ZArith NArith List Zpower.

Inductive hex_digit : Set :=
| Hx0 | Hx1 | Hx2 | Hx3
| Hx4 | Hx5 | Hx6 | Hx7
| Hx8 | Hx9 | HxA | HxB
| HxC | HxD | HxE | HxF
.

Inductive hex_digit_partial : Set :=
| HDP0 | HDP1 (b: bool)
| HDP2 (b1 b0: bool)
| HDP3 (b2 b1 b0: bool)
.

Definition hex_partial_as_digit (hp: hex_digit_partial) : hex_digit :=
  match hp with
    | HDP0
    | HDP1 false
    | HDP2 false false
    | HDP3 false false false => Hx0
    | HDP1 true
    | HDP2 false true
    | HDP3 false false true => Hx1
    | HDP2 true false
    | HDP3 false true false => Hx2
    | HDP2 true true
    | HDP3 false true true => Hx3
    | HDP3 true false false => Hx4
    | HDP3 true false true => Hx5
    | HDP3 true true false => Hx6
    | HDP3 true true true => Hx7
  end.

Definition set_next_bit (bh: hex_digit_partial)
  : hex_digit + hex_digit_partial :=
  match bh with
    | HDP0 => inr _ (HDP1 true)
    | HDP1 b => inr _ (HDP2 true b)
    | HDP2 b1 b0 => inr _ (HDP3 true b1 b0)
    | HDP3 b2 b1 b0 => inl _
      (match b2, b1, b0 with
         | false, false, false => Hx8
         | false, false, true  => Hx9
         | false, true , false => HxA
         | false, true , true  => HxB
         | true , false, false => HxC
         | true , false, true  => HxD
         | true , true , false => HxE
         | true , true , true  => HxF
       end)
  end.

Definition reset_next_bit (bh: hex_digit_partial)
  : hex_digit + hex_digit_partial :=
  match bh with
    | HDP0 => inr _ (HDP1 false)
    | HDP1 b => inr _ (HDP2 false b)
    | HDP2 b1 b0 => inr _ (HDP3 false b1 b0)
    | HDP3 b2 b1 b0 => inl _
      (match b2, b1, b0 with
         | false, false, false => Hx0
         | false, false, true  => Hx1
         | false, true , false => Hx2
         | false, true , true  => Hx3
         | true , false, false => Hx4
         | true , false, true  => Hx5
         | true , true , false => Hx6
         | true , true , true  => Hx7
       end)
  end.

Definition hex_num : Set := list hex_digit.

Fixpoint hex_of_pos' (p: positive) (curr: hex_digit_partial) (acc: hex_num)
  {struct p} : hex_num :=
  match p with
    | xH => match set_next_bit curr with
              | inl d => d
              | inr hp => hex_partial_as_digit hp
            end :: acc
    | xO p' => match reset_next_bit curr with
                 | inl d => hex_of_pos' p' HDP0 (d::acc)
                 | inr hp => hex_of_pos' p' hp acc
               end
    | xI p' => match set_next_bit curr with
                 | inl d => hex_of_pos' p' HDP0 (d::acc)
                 | inr hp => hex_of_pos' p' hp acc
               end
  end.

Definition hex_of_pos (p: positive) : hex_num :=
  hex_of_pos' p HDP0 nil.

Section PRINT.

  Require Import Ascii String.
  Local Open Scope char_scope.

  Definition hex_digit_ascii (hx: hex_digit) : ascii :=
    match hx with
      | Hx0 => "0" | Hx1 => "1"
      | Hx2 => "2" | Hx3 => "3"
      | Hx4 => "4" | Hx5 => "5"
      | Hx6 => "6" | Hx7 => "7"
      | Hx8 => "8" | Hx9 => "9"
      | HxA => "A" | HxB => "B"
      | HxC => "C" | HxD => "D"
      | HxE => "E" | HxF => "F"
    end.

  Fixpoint hex_num_string (hn: hex_num) {struct hn} : string :=
    match hn with
      | d :: hn' => String (hex_digit_ascii d) (hex_num_string hn')
      | nil => EmptyString
    end.

  Definition print_pos (p: positive) : string :=
    ("0x" ++ hex_num_string (hex_of_pos p))%string.

  Definition string_of_z (z: Z) : string :=
    (match z with
     | Z0 => "0"
     | Zpos p => print_pos p
     | Zneg p => "-" ++ print_pos p
     end)%string.

End PRINT.
