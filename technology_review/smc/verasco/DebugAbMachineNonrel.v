Require Import
  Utf8 String ToString
  Integers 
  LatticeSignatures
  AbMachineNonrel
  AdomLib
  IntervalDomain.

Parameter print_string : string → unit.

Definition print {A} : string → A → A :=
  fun s x =>
  let () := print_string s in
  x.

Lemma print_id {A} s (x: A) : print s x = x.
Proof. now unfold print; destruct print_string. Qed.

Local Open Scope string_scope.

Definition print_leb (x y: string) (r: bool) : string :=
  x ++ " ⊑ " ++ y ++ " → " ++ (if r then "tt" else "ff").

Definition print_join (x y z: string) : string :=
  x ++ " ⊔ " ++ y ++ " → " ++ z.

Definition print_widen (x y z: string) : string :=
  x ++ " ∇ " ++ y ++ " → " ++ z.

Definition print_meet (x y z: string) : string :=
  x ++ " ⊓ " ++ y ++ " → " ++ z.

Definition string_of_int_unop (op: int_unary_operation) : string :=
  match op with
  | OpNeg => "-"
  | OpNot => "¬"
  end.

Definition string_of_comparison (cmp: comparison) : string :=
  match cmp with
  | Ceq => " = "
  | Cne => " ≠ "
  | Clt => " < "
  | Cle => " ≤ "
  | Cge => " ≥ "
  | Cgt => " > "
  end.

Definition string_of_int_binop (op: int_binary_operation) : string :=
  match op with
  | OpAdd => " + "
  | OpSub => " − "
  | OpMul => " × "
  | OpDivs=> " ÷ "
  | OpShl => " << "
  | OpShr => " >> "
  | OpShru => " >>u "
  | OpAnd => " & "
  | OpOr  => " | "
  | OpXor => " ^ "
  | OpCmp c => string_of_comparison c
  | OpCmpu c => string_of_comparison c
  end.

Instance int_unary_operation_to_string : ToString int_unary_operation := string_of_int_unop.
Instance int_binary_operation_to_string : ToString int_binary_operation := string_of_int_binop.

Definition print_int_unop (op: int_unary_operation) (x y: string) : string :=
  to_string op ++ x ++ " → " ++ y.

Definition print_int_binop (op: int_binary_operation) (x y z: string) : string :=
  x ++ to_string op ++ y ++ " → " ++ z.

Definition print_backward_int_unop (op: int_unary_operation) (x y x': string) : string :=
  to_string op ++ x ++ " = " ++ y ++ " → " ++ x'.

Definition print_backward_int_binop (op: int_binary_operation) (x y z x' y': string) : string :=
  x ++ to_string op ++ y ++ " = " ++ z ++ " → " ++ "(" ++ x' ++ ", " ++ y' ++ ")".

Definition string_of_sign_flag (s:signedness) : string :=
  match s with
    | Signed => "Signed"
    | Unsigned => "Unsigned"
  end.

Section ADOM.

Context {t t': Type} WL G (D: adom t t' WL G) `{ToString t}.

Instance debug_wlat : weak_lattice t :=
  { leb x y := let r := leb x y in
               let s := print_leb (to_string x) (to_string y) r in
               print s r
  ; top := top
  ; join x y := let r := join x y in
                let s := print_join (to_string x) (to_string y) (to_string r) in
                print s r
  ; widen x y := let r := widen x y in
                 let s := print_widen (to_string x) (to_string y) (to_string r) in
                 print s r
  }.

Lemma debug_adom : adom t t' debug_wlat G.
Proof.
  split.
  intros x y; simpl; rewrite print_id. apply gamma_monotone; auto.
  simpl. apply gamma_top; auto.
  intros x y; simpl; rewrite print_id. apply join_sound; auto.
Qed.

End ADOM.

Section S.

Context {t_int: Type} (dom: ab_machine_int t_int)
        {dom_correct: ab_machine_int_correct dom}
        `{ToString t_int}.

Instance debug_ab_machine_int : ab_machine_int t_int :=
  { as_int_wl := debug_wlat _
  ; as_int_adom := debug_adom _ _ as_int_adom
  ; meet_int x y := let r := meet_int x y in
                let s := print_meet (to_string x) (to_string y) (to_string r) in
                print s r
  ; size := size
  ; concretize ab :=
      let r : IntSet.fint_set := concretize ab in
      let s : string := ("concretize: " ++ to_string ab)%string in
      print s r
  ; const_int := const_int
  ; booleans := booleans
  ; range_int := range_int
  ; forward_int_unop op x :=
      let r : t_int+⊥ := forward_int_unop op x in
      let s : string := print_int_unop op (to_string x) (to_string r) in
      print s r
  ; forward_int_binop op x y :=
      let r : t_int+⊥ := forward_int_binop op x y in
      let s : string := print_int_binop op (to_string x) (to_string y) (to_string r) in
      print s r
  ; is_in_itv := is_in_itv
  ; backward_int_unop op x y :=
      let r := backward_int_unop op x y in
      let s := print_backward_int_unop op (to_string x) (to_string y) (to_string r) in
      print s r
  ; backward_int_binop op x y z :=
      let (r1, r2) := backward_int_binop op x y z in
      let s := print_backward_int_binop op (to_string x) (to_string y) (to_string z) (to_string r1) (to_string r2) in
      print s (r1, r2)
  }.

Instance debug_ab_machine_int_correct : ab_machine_int_correct debug_ab_machine_int.
Proof.
  destruct dom_correct. clear dom_correct.
  constructor; auto;
  simpl; intros;
  repeat rewrite print_id;
  auto.
  generalize (backward_int_binop_sound op x y z i j).
  match goal with |- context[let '(_,_) := ?a in _] => destruct a end.
  rewrite print_id; auto.
Qed.

End S.
