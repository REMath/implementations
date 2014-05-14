Require Import ssreflect ssrbool ssrnat eqtype seq fintype.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import SPred septac spec spectac safe basic program.
Require Import instr instrsyntax decinstr instrrules reader pointsto cursor.
Require Import tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

(* Macro for a multiway switch with fall-through.
   This version is parametric in the eqType of value being tested and the way that value is represented in the state
   The macro takes as input a single-arm equality test
*)

Section Switchmacro.

(* Variables needed for generating the actual code *)
Variable valuetype : eqType.
Variable testcode : valuetype -> DWORD -> program.

(* Variables needed for formalizing correctness *)
Variable paramtype : Type.
Variable valuepred : paramtype -> valuetype -> SPred.

(* This is the generalized spec for one-armed branch-if-equals
   See condbrDwordStarEAX lower down for an example its instantiation 

   Note that there's already a subtle awkwardness about existentials, though:
   If we define valuepred v as (Exists p, EAX ~= p ** p :-> v ** ..), as seems natural, then the Exists p 
   could be instantiated differently in the pre and post conditions which would totally mess up modularity 
   - in this particular case we want to know that EAX is preserved in order to glue the multiple tests together
   as well as to integrate with some larger context. Hence we explicitly parameterize by a "p" of type
   paramtype, which in general could be any type
*)
Definition condbrspec (b:valuetype) dest := 
    Forall p, Forall v, Forall i, Forall j, 
     (safe @ ( (v:valuetype) == b /\\ EIP ~= dest) //\\
      safe @ (((v != b)) /\\ EIP ~= j)
      -->>
     safe @ (EIP ~= i))
      @  (valuepred p v) 
     <@ (i -- j :-> testcode b dest).



(* This is a macro for generating n-way switch statements
   It takes a list of pairs, each of which has a first component
   that is a value to test against and a second component that is
   a label to jump to if the test value matches that
   case. If no value in the table matches, then the code falls through
*)
Fixpoint switch (vsbrs : list (valuetype * DWORD)) : program :=
if vsbrs is (v,br)::rest then testcode v br ;; switch rest else prog_skip.  

(* This is the precondition associated with such a table, saying for a
   value x that it's safe to jump to label br_i if x = v_i
*)
Fixpoint table_precond (vsbrs : list (valuetype * DWORD)) (x: valuetype) : spec :=
if vsbrs is (v,br)::rest then (safe @ (x == v /\\ EIP ~= br)) //\\ table_precond rest x
else ltrue.

(* And here's the spec for a full switch statement, including the
   requirement that it be safe to fall through if the value is not in the list
*)
Definition table_precond_all (vsbrs : seq (valuetype*DWORD)) (x:valuetype) :=
Forall p, Forall x, Forall i, Forall j, 
 (table_precond vsbrs x //\\ safe @ (x \notin [seq fst i | i<-vsbrs] /\\ EIP ~=j)
  -->>
 safe @ (EIP ~= i))
 @ (valuepred p x) (* was (EAX ~= p ** EDI? ** p :-> x ** OSZCP_Any) *)
 <@ (i -- j :-> switch vsbrs).

(* little lemma about sequence membership *)
Lemma footle (x y : valuetype) ys : (x \notin y :: ys) = ((x != y) && (x \notin ys)).
rewrite in_cons.
rewrite negb_or.
reflexivity.
Qed.

(* Now prove the generic version of correctness for multiway switch.
   Not quite sure about using Coq implication here, rather than internalizing in the spec logic...
*)
Lemma switchlemma : 
  (forall b dest, |-- condbrspec b dest) -> 
   (forall vsbrs x,  |-- table_precond_all vsbrs x).
move => Hbranchspec vsbrs x.
elim: vsbrs x => [| [v br] rest IHrest] x.
rewrite /table_precond_all.
specintros => p x0 i j. 
(* here just need to know that i=j as program is empty, and that the notin is trivial *)
rewrite /memIs /=.
specintro => <-.
rewrite <- spec_reads_frame.
rewrite <- spec_frame.
apply: limplAdj.
apply landL2. 
apply landL2.
cancel1.
by sbazooka.

rewrite /table_precond_all /=.
specintros => p v0 i j.
unfold_program.
specintro => imid.
(* here we use the hypothesis *)
rewrite /condbrspec in Hbranchspec.
specapply Hbranchspec.
by ssimpl.
specsplit.
(* this proof state should totally fall to automation - it's really tedious to do by hand *)
autorewrite with push_at.
rewrite <- spec_reads_frame.
apply: limplAdj.
apply landL2.
apply landL1.
apply landL1.
cancel1.
by sbazooka.

(* now for the inductive case *)

rewrite /table_precond_all in IHrest.

rewrite <- spec_reads_merge.
rewrite spec_reads_swap.
rewrite <- spec_reads_frame.
(* Note that we had to do the above messing about to make this specapply
   pick up the right thing
*)
rewrite spec_at_emp.
specintros => Neq.
specapply (IHrest v0).

sbazooka.

rewrite <- spec_reads_frame.
rewrite -> limplValid.
autorewrite with push_at.
specsplit.
apply landL1.
apply landL2.


rewrite -[X in _ |-- X]spec_at_at. 
apply spec_frame. 
(* Alternative: rewrite -!spec_at_at. apply spec_frame.
   Note that {2} doesn't work here as the first occurence of the pattern messes up the unification, I think  
*)
apply landL2.
rewrite footle.
cancel1.
sdestructs =>  ->. 
rewrite Neq.
by sbazooka.
Qed.


End Switchmacro.


(* Now the concrete instantiations *)

(* This is one concrete example of an one-arm equality test and branch, for DWORDs, with the value being pointed to by EAX
   (Using intermediate move because of missing CMP rule and gratuitously trashing EDI in the process)
*)

Definition ifEqDwordStarEAX (b:DWORD) (dest:DWORD) : program :=
  MOV EDI, [EAX];;
  CMP EDI, b;;
  JE dest.

Lemma condbrDwordStarEAX (b:DWORD) dest : 
    |-- condbrspec ifEqDwordStarEAX (fun p => fun (v:DWORD) => (EAX ~= p ** EDI? ** p :-> v ** OSZCP_Any)) b dest.
Proof.
rewrite /ifEqDwordStarEAX /condbrspec.
specintros => p v i j.
unfold_program. specintros => i1 i2.

specapply MOV_RM0_rule.
by ssimpl.

elim E: (sbbB false v b) => [carry res].
have E': subB v b = res by rewrite /subB E. 
specapply CMP_RI_rule; last eassumption.
by ssimpl.

rewrite -E' subB_eq0. 

specapply JZ_rule.
rewrite /OSZCP.
by ssimpl.

specsplit.
rewrite <- spec_reads_frame.
rewrite <- spec_later_weaken.
autorewrite with push_at.
apply limplValid.
apply landL1.
cancel1.

sdestructs =>/eqP ->.
rewrite /OSZCP_Any /flagAny /regAny.
by sbazooka.

rewrite <- spec_reads_frame.
autorewrite with push_at.
apply limplValid.
apply landL2.
cancel1.
sdestructs =>/eqP ->.
rewrite /OSZCP_Any /flagAny /regAny.
by sbazooka.
Qed.

Section ByteEq.
Variable r : BYTEReg.

Definition ifEqByter (b:BYTE) (dest:DWORD) : program :=
  (BOP false OP_CMP (DstSrcRI false r b));; (* syntax could do with improvement! *)
  JE dest.

Lemma condbrByter (b:BYTE) dest : 
  |-- condbrspec ifEqByter (fun (p:unit) => fun (v:BYTE) => (BYTEregIs r v ** OSZCP_Any)) b dest.
Proof.
rewrite /ifEqByter /condbrspec.
specintros => _ v i j.
unfold_program.
specintros => i'.

specapply CMP_RbI_eq_rule.
by ssimpl.

specapply JZ_rule.
sbazooka.

rewrite /OSZCP_Any. 
specsplit; rewrite <- spec_reads_frame; autorewrite with push_at.
rewrite <- spec_later_weaken.
apply limplValid.
apply landL1.
cancel1.
sdestructs =>/eqP ->.
rewrite /flagAny. 
by sbazooka.

apply limplValid; apply landL2.
cancel1.
sdestructs =>/eqP ->.
rewrite /flagAny.
by sbazooka.
Qed.
End ByteEq.

(* Abstract sequences and iterators *)

(* Not sure this is the best way to divide things up
   Could allow valis to share storage with the seqsplit predicate by making it ternary
   and maybe next should load the current value and increment the cursor at the same time
*)
Structure iter := mkiter {
 T : eqType;
 seqsplit : seq T -> seq T -> SPred;
 current : program;
 next : program;
 valis : option T -> SPred; (* this doesn't have the extra parameter in at the moment *)
 valany : SPred;
 valisisany : forall v, valis v |-- valany;
 curnil : forall s1, 
   |-- basic (valany ** seqsplit s1 [::]) current (valis None ** seqsplit s1 [::]);
 curcons : forall s1 v s2, 
   |-- basic (valany ** seqsplit s1 (v::s2)) current (valis (Some v) ** seqsplit s1 (v::s2));
 nextcons : forall s1 v s2,
   |-- basic (seqsplit s1 (v::s2)) next (seqsplit (s1 ++ [:: v]) s2) (* frame on valis/any of course *)
}.

Definition NZBYTE := {x : BYTE | x != #0}.
Variable start : DWORD.
Section foo.
Context {X} {MX : MemIs X}.

Global Instance subtypememis P : MemIs {x : X | P x} := fun p q v => p -- q :-> sval v.
End foo.

Definition byteseqsplit (s1 s2 : seq NZBYTE) := 
 Exists q, Exists r, EAX ~= q ** start -- q :-> s1 ** q -- r :-> s2 ** r :-> (#0 : BYTE).

Variable r : BYTEReg.
Definition bytecurrent : program := (MOV r, [EAX + 0]).

Definition bytenext : program := (INC EAX).

Definition bytevalis (v : option NZBYTE) :=
 match v with | None => (BYTEregIs r #0)
              | Some b => (BYTEregIs r (sval b))
 end.

Definition bytevalany := Exists v, BYTEregIs r v.

Lemma bytevalisisany : forall v, bytevalis v |-- bytevalany.
elim=> [a |]; rewrite /bytevalis /bytevalany; sbazooka.
Qed.

Lemma bytecurnil : forall s1, 
   |-- basic (bytevalany ** byteseqsplit s1 [::]) bytecurrent (bytevalis None ** byteseqsplit s1 [::]).
move =>s; rewrite /bytevalany /byteseqsplit /bytecurrent /bytevalis.
specintros => v q last.
basicapply MOV_RMb_rule.
rewrite seqMemIs_nil.
rewrite addB0.
sdestruct.
rewrite seqMemIs_nil.
move => H; rewrite H.
sbazooka.
Qed.

Lemma bytecurcons : forall s1 v s2, 
   |-- basic (bytevalany ** byteseqsplit s1 (v::s2)) bytecurrent (bytevalis (Some v) ** byteseqsplit s1 (v::s2)).
move => s1 v s2; rewrite /bytevalany /byteseqsplit /bytecurrent /bytevalis. 
specintros => v0 q last.
rewrite seqMemIs_cons.
specintros => p'.
(* at this point, I should know that p' is q+1 *)
setoid_rewrite memIsBYTE_next_entails.
specintro => H.
rewrite H.
basicapply MOV_RMb_rule; rewrite addB0.
(* rewrite {3}/memIs. *)
rewrite {2}/pointsTo.
by sbazooka.
ssimpl.
rewrite seqMemIs_cons.
sbazooka.
rewrite /pointsTo.
sdestruct => q'.
setoid_rewrite (@memIsBYTE_next_entails q q' (sval v)).
sdestruct => HH.
rewrite HH.
rewrite {2}/memIs /subtypememis.
sbazooka.
Qed.

(* that was a bit more of a slog than it could have been - I'm only loading a single byte! *)

Lemma ptnothwm (cur : Cursor 32) (b:BYTE) : cur :-> b |-- Exists bits, cur = mkCursor bits /\\ cur :-> b.
elim cur.
move =>b0.
sbazooka.
rewrite {1}/pointsTo.
setoid_rewrite interpReader_bindBYTE_hwm.
sdestructs => _.
apply lfalseL.
Qed.

Lemma bytenzbyteseq (s : seq NZBYTE) : forall (p q : Cursor 32),
 p -- q :-> s -|- p -- q :-> map sval s.
elim s.
rewrite /memIs //=.

(* split; sbazooka. *)
(* rewrite /memIs  //=. *)
move => a l IH p q.
rewrite /memIs //=.
split; sdestruct => p'.
rewrite {1}/memIs /subtypememis.
sbazooka.
apply IH.
rewrite {3}/memIs /subtypememis.
sbazooka.
apply IH.
Qed.
Lemma silly (P : SPred) : P |-- P.
sbazooka.
Qed.



Lemma seqhwm (c:Cursor 32) (p:DWORD) (s:seq NZBYTE) : c -- p :-> s |-- c != hwm 32 /\\ c -- p :-> s.
elim c => [b|].
sbazooka.
rewrite {1}bytenzbyteseq.
setoid_rewrite (@seq_BYTE_hwm p [seq sval i | i <- s]).
apply lfalseL.
Qed.

Lemma app1 : forall (s : seq BYTE) (p q : DWORD) b, q != ones 32 ->  p -- q :-> s ** q -- incB q :-> b |-- p -- incB q :-> (s ++ [:: b])%SEQ.
elim => [| h t IH] p q b Hq.
rewrite /cat.
rewrite seqMemIs_nil.
sdestructs => ->.
rewrite memIs_consBYTE.
rewrite /cursor.next.
ssimpl.
rewrite (negbTE Hq).
rewrite seqMemIs_nil.
rewrite /pointsTo.
sbazooka.
(* now the inductive case *)
rewrite /cat -/cat.
rewrite memIs_consBYTE.
rewrite memIs_consBYTE.
ssimpl.
(* so now can almost apply induction hypothesis, but need to know p is not ones 32 so next p is inc P *)
elim (cursor.next p).
move => np.
apply (IH np q b Hq).
setoid_rewrite (@seq_BYTE_hwm q t). 
sbazooka.
Qed.

Lemma bytenextcons : forall s1 v s2,
   |-- basic (byteseqsplit s1 (v::s2)) bytenext (byteseqsplit (s1 ++ [:: v]) s2) @ OSZCP_Any.
move => s1 v s2; rewrite /byteseqsplit /bytenext.
specintros => q last.
rewrite seqMemIs_cons.
specintros => p'.
setoid_rewrite memIsBYTE_next_entails.
specintro => ->.
autorewrite with push_at.
(* here we know the crucial fact that last :-> #0 which means that cursor.next q can't be hwm
   This important information is, by default, thrown away by just using basicapply here :-(
*)
setoid_rewrite (@ptnothwm last #0).
specintros => lastbits lasteqn.
rewrite lasteqn.

setoid_rewrite (@seqhwm (cursor.next q)).
specintros => Hseq.
basicapply (@INC_R_ruleNoFlags EAX q).
rewrite /cursor.next.
(* So now we know that last is not hwm, so q can't be ones 32 (note s2 might be empty so inc q == last) *)
elim: (q == ones 32).
(* this is the contradictory case want to apply seq_BYTE_hwm but seq BYTE mismatches with seq NZBYTE *)
(* this doesn't help: rewrite {3}/memIs /subtypememis. *)
rewrite [hwm 32 -- lastbits :-> s2]bytenzbyteseq.
setoid_rewrite seq_BYTE_hwm.
sbazooka.
(* don't ssimpl at this point - loses information that next q isn't hwm (so inc q isn't zero) *)
(* now down to the real result about adding something to the end of the sequence *)
ssimpl. 

rewrite bytenzbyteseq.
rewrite bytenzbyteseq.
rewrite map_cat.
eapply app1.
move: Hseq. 
rewrite /cursor.next. 
case (q == ones 32).
by [].
rewrite //=.
Qed.

