Require Import
  Coqlib Utf8 String
  Integers ToString
  LatticeSignatures AbMachineNonrel
  DebugAbMachineNonrel
  Goto GotoSem GotoString AbGoto.

Section S.

Local Open Scope string_scope.

Context {t d: Type} (D: ab_machine_int d) (M:mem_dom t d) `{ToString t} `{ToString d}.

Definition print_var (r: register) (v: string) : string :=
  string_of_reg r ++ " → " ++ v.

Definition print_load (x: int) (v: string) : string :=
  "[" ++ string_of_int x ++ "] → " ++ v.

Definition print_store (dst: string) (v: string) (res: t) : string :=
  "[" ++ dst ++ "] := " ++ v ++ " ⇒ " ++ (to_string res).

Definition print_assign (rd: register) (v: string) : string :=
  string_of_reg rd ++ " := " ++ v.

Definition print_compare (rs rd: register) : string :=
  string_of_reg rs ++ " ≥ " ++ string_of_reg rd.

Definition debug_mem_dom : mem_dom t d :=
  {| as_wl := debug_wlat (as_wl M)
  ; var x v := let r := var M x v in
               let s := print_var v (to_string r) in
               print s r
  ; load_single x v := let r := load_single M x v in
                       let s := print_load v (to_string r) in
                       print s r
  ; store_single x y z := let r := store_single M x y z in
                          let s := print_store (to_string y) (to_string z) r in
                          print s r
  ; assign x y z := let r := assign M x y z in
                    let s := print_assign y (to_string z) in
                    print s r
  ; compare x rs rd := let r := compare M x rs rd in
                       let s := print_compare rs rd in
                       print s r
  ; assume := assume M
  ; init := init M
  |}.

Variable G : gamma_op t machine_config.
Hypothesis M_sound: mem_dom_sound M G.

Lemma debug_mem_dom_sound : mem_dom_sound debug_mem_dom G.
Proof.
  destruct M_sound.
  constructor; simpl; auto;
  intros; repeat rewrite print_id; eauto.
  apply debug_adom; auto.
Qed.

End S.
