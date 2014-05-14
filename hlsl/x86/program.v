Require Import ssreflect ssrbool ssrnat eqtype seq fintype.
Require Import bitsrep instr decinstr reader SPred pointsto cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive program :=
  prog_instr (c: Instr)
| prog_skip
| prog_seq (p1 p2: program)
| prog_declabel (body: DWORD -> program)
| prog_label (l: DWORD).

Coercion prog_instr: Instr >-> program.

(* Instructions in instrsyntax are up to level 40, so delimiters need to be
   above that. *)
Infix ";;" := prog_seq (at level 42, right associativity).
Notation "'LOCAL' l ';' p" := (prog_declabel (fun l => p))
  (at level 45, l ident, right associativity).
Notation "l ':;'" := (prog_label l)
  (at level 8, no associativity, format "l ':;'").
Notation "l ':;;' p" := (prog_seq (prog_label l) p)
  (at level 8, p at level 45, right associativity,
   format "l ':;;'  p").

(* The match-clauses here are theoretically redundant, but they make this
   definition unfold to something more directly useful for rewriting. *)
Instance programMemIs : MemIs program := fix F i j prog :=
  match prog with
  | prog_instr c => i -- j :-> c
  | prog_skip =>
      match i, j with
      | mkCursor i, mkCursor j => i = j /\\ empSP
      | _, _                   => i = j /\\ empSP
      end
  | prog_seq p1 p2 => Exists i': DWORD, F i i' p1 ** F i' j p2
  | prog_declabel body => Exists l, F i j (body l)
  | prog_label l =>
      match i, j with
      | mkCursor i, mkCursor j =>
                i = j /\\ i = l /\\ empSP
      | _, _ => i = j /\\ i = l /\\ empSP
      end
  end.

