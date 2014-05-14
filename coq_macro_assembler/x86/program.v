Require Import ssreflect ssrbool ssrnat eqtype seq fintype.
Require Import bitsrep instr decinstr SPred pointsto cursor reader writer roundtrip.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*=program *)
Inductive program :=
  prog_instr (c: Instr)
| prog_skip | prog_seq (p1 p2: program)
| prog_declabel (global: option String.string) (body: DWORD -> program)
| prog_label (l: DWORD)
| prog_data {T} {R: Reader T} {W: Writer T} 
                (RT: Roundtrip R W) (v: T).
Coercion prog_instr: Instr >-> program.
(*=End *)

Require Import tuple. 

(* Instructions in instrsyntax are up to level 60, so delimiters need to be
   above that. *)
Infix ";;" := prog_seq (at level 62, right associativity).
Notation "'LOCAL' l ';' p" := (prog_declabel None (fun l => p))
  (at level 65, l ident, right associativity).
(* This notation is not ideal, we could enclose the name between two semicolons
   for compatibility with MASM. I do not think there is a way to get a string
   out of the binder only. *)
Notation "'GLOBAL' l n ';' p" := (prog_declabel (Some n) (fun l => p))
  (at level 65, l ident, right associativity).
Notation "l ':;'" := (prog_label l)
  (at level 8, no associativity, format "l ':;'").
Notation "l ':;;' p" := (prog_seq (prog_label l) p)
  (at level 8, p at level 65, right associativity,
   format "l ':;;'  p").

(*=dd *)
Definition db := prog_data RoundtripBYTE.
Definition dw := prog_data RoundtripWORD.
Definition dd := prog_data RoundtripDWORD.
(*=End *)
Definition ds s := prog_data (@RoundtripTupleBYTE (String.length s)) (stringToTupleBYTE s).
Definition align m := prog_data (RoundtripAlign m) tt. 
Definition pad m := prog_data (RoundtripPad m) tt. 

(* Sometimes handy just to get nice output *)
Fixpoint linearizeWith (p: program) tail :=
  match p with
  | prog_skip => tail
  | prog_seq p1 p2 => linearizeWith p1 (linearizeWith p2 tail)
  | prog_declabel g f => prog_declabel g (fun d => linearizeWith (f d) tail)
  | _ => if tail is prog_skip then p else prog_seq p tail
  end.
Definition linearize p := linearizeWith p prog_skip.


Instance interpProgram : MemIs program := fix interpProgram i j prog :=
  match prog with
  | prog_instr c => i -- j :-> c
  | prog_skip =>
      match i, j with
      | mkCursor i, mkCursor j => i = j /\\ empSP
      | _, _                   => i = j /\\ empSP
      end
  | prog_seq p1 p2 => Exists i': DWORD, @memIs _ interpProgram i i' p1 ** @memIs _ interpProgram i' j p2
  | prog_declabel _ body => Exists l, @memIs _ interpProgram i j (body l)
  | prog_label l =>
      match i, j with
      | mkCursor i, mkCursor j =>
                i = j /\\ i = l /\\ empSP
      | _, _ => i = j /\\ i = l /\\ empSP
      end
  | prog_data _ _ _ _ v => i -- j :-> v
  end.

Module ProgramTactic.

  (* This is identical to prod/pair/fst/snd from the standard library, repeated
     here to ensure we have full control over the fs and sn names. Then we can
     safely unfold them with cbv without affecting unrelated user declarations.
   *)
  Record pr A B := pa { fs: A; sn: B }.

  (* This helper tactic takes a memIs assertion and returns an unfolded one. *)
  (* This uses the trick from CPDT in the chapter "Building a Reification Tactic
     that Recurses Under Binders" *)
  Ltac aux P :=
    let P := eval cbv [fs sn] in P in
    match P with
    | fun (x: ?X) => @?i x -- @?j x :-> (@?p1 x ;; @?p2 x) =>
        let P1 := aux (fun i'x: pr DWORD X => i (sn i'x) -- fs i'x :-> p1 (sn i'x)) in
        let P2 := aux (fun i'x: pr DWORD X => fs i'x -- j (sn i'x) :-> p2 (sn i'x)) in
        constr:(fun (x:X) => Exists i': DWORD, P1 (pa i' x) ** P2 (pa i' x))
    | fun (x: ?X) => @?i x -- @?j x :-> (@?l x :;) =>
        (* It's a bit lazy to just rely on unfold here, but it works in
           practice. *)
        let P := eval unfold memIs, interpProgram in P in
        constr:P
    | fun (x: ?X) => @?i x -- @?j x :-> (prog_instr (@?c x)) =>
        let P := eval unfold memIs, interpProgram in P in
        constr:P
    | fun (x: ?X) => @?i x -- @?j x :-> (prog_data (@?c x)) =>
        let P := eval unfold memIs, interpProgram in P in
        constr:P
    | fun (x: ?X) => @?i x -- @?j x :-> (prog_skip :;) =>
        let P := eval unfold memIs, interpProgram in P in
        constr:P
    | fun (x: ?X) => @?i x -- @?j x :-> (prog_declabel _ (@?body x)) =>
        let P' := aux (fun lx: pr DWORD X =>
                      i (sn lx) -- j (sn lx) :-> body (sn lx) (fs lx)) in
        constr:(fun (x:X) => Exists l, P' (pa l x))
    | _ => P
    end.

  Ltac unfold_program :=
    match goal with
    | |- context C [ @memIs _ interpProgram ?i ?j ?p ] =>
        let e := aux (fun (_: unit) => @memIs _ interpProgram i j p) in
        let e := eval cbv [fs sn] in (e tt) in
        let g := context C [e] in
        change g
    end.
End ProgramTactic.

(* This tactic essentially just unfolds the definition of interpProgram.
   Because of typeclass complications, this cannot just be done with standard
   tactics. *)
Ltac unfold_program := ProgramTactic.unfold_program.

(*---------------------------------------------------------------------------
    Structural equivalence on programs, capturing monoidal sequencing and
    scope extrusion    
  ---------------------------------------------------------------------------*)
Definition liftEq T U (eq: T -> T -> Prop) := fun (f g: U -> T) => forall u, eq (f u) (g u). 
Inductive progEq : program -> program -> Prop :=
| progEqRefl:  forall p, progEq p p
| progEqSym:   forall p1 p2, progEq p1 p2 -> progEq p2 p1
| progEqTrans: forall p1 p2 p3, progEq p1 p2 -> progEq p2 p3 -> progEq p1 p3
| progEqDecLabel: forall g p q, (liftEq progEq p q) -> progEq (prog_declabel g p) (prog_declabel g q)
| progEqSeq:   forall p1 p2 q1 q2, progEq p1 q1 -> progEq p2 q2 -> progEq (prog_seq p1 p2) (prog_seq q1 q2)
| progEqSeqAssoc: forall p1 p2 p3, progEq (p1;;p2;;p3) ((p1;;p2);;p3)
| progEqSeqSkip: forall p, progEq (p;;prog_skip) p
| progEqSkipSeq: forall p, progEq (prog_skip;;p) p
| progEqSeqDecLabel: forall g p f, progEq (p;; prog_declabel g f) (prog_declabel g (fun l => p;; f l))
| progEqDecLabelSeq: forall g p f, progEq (prog_declabel g f;; p) (prog_declabel g (fun l => f l;; p))
| progEqDecLabelSkip: forall g, progEq (prog_declabel g (fun l => prog_skip)) prog_skip.

(* Add progEq as an instance of Equivalence for rewriting *)
Require Import Setoid Morphisms RelationClasses. 
Global Instance progEqEqu : Equivalence progEq.
Proof. constructor; red. 
+ apply progEqRefl. 
+ apply progEqSym. 
+ apply progEqTrans. 
Qed. 

(* Declare morphisms for context rules *)
Global Instance progEq_seq_m:
  Proper (progEq ==> progEq ==> progEq) prog_seq. 
Proof. move => p1 p2 EQ1 q1 q2 EQ2 . by apply progEqSeq. Qed. 

Global Instance progEq_decLabel_m:
  Proper (eq ==> liftEq progEq ==> progEq) prog_declabel.
Proof. move => g1 g2 EQ1 f1 f2 EQ2. rewrite EQ1. by apply progEqDecLabel. Qed. 

(* Main lemma: memIs respects progEq *)
Require Import septac.
Lemma memIsProgEquiv p1 p2 : progEq p1 p2 -> forall (l l':DWORD), memIs l l' p1 -|- memIs l l' p2. 
Proof. move => EQ. induction EQ => l l'. 
(* progEqRefl *)
+ done.
(* progEqSym *)
+ by rewrite IHEQ. 
(* progEqTrans *)
+ by rewrite IHEQ1 IHEQ2. 
(* progEqDecLabel *)
+ rewrite /memIs/=. split. sdestruct => lab. ssplit. rewrite H0. reflexivity. 
sdestruct => lab. ssplit. rewrite -H0. reflexivity. 
(* progEqSeq *)
+ unfold_program. unfold_program. split; sdestruct => i. rewrite IHEQ1 IHEQ2; sbazooka. 
rewrite -IHEQ1 -IHEQ2; sbazooka. 
(* progEqSeqAssoc *)
+ unfold_program. unfold_program. split; sbazooka. 
(* progEqSeqSkip *)
+ unfold_program. do 3 rewrite /memIs/=. split. sdestruct => s. sdestruct => ->. sbazooka. sbazooka. 
(* progEqSkipSeq *)
+ unfold_program. do 3 rewrite /memIs/=. split. sdestruct => s. sdestruct => ->. sbazooka. sbazooka. 
(* progEqSeqDecLabel *)
+ unfold_program. do 3 rewrite /memIs/=. split; sbazooka. 
(* progEqDecLabelSeq *)
+ unfold_program. do 3 rewrite /memIs/=. split; sbazooka. 
(* progEqDecLabelSkip *)
+ unfold_program. split. sdestruct => _. reflexivity. sbazooka. 
Qed. 

(* Now declare memIs as a morphism wrt progEq *)
Global Instance memIs_progEq_m (p p': DWORD):
  Proper (progEq ==> lequiv) (@memIs _ _ p p'). 
Proof. move => p1 p2 EQ. by apply memIsProgEquiv. Qed. 


