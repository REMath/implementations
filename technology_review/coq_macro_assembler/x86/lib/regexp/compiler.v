Require Import ssreflect ssrfun ssrbool finfun fintype ssrnat eqtype seq tuple.
Require Import path fingraph  finset.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program macros call.
Require Import instr monad reader writer procstate procstatemonad mem exn eval decinstr
               monadinst ioaction bitsrep bitsops eval step encinstr pointsto cursor.
Require Import program programassem reg instrsyntax instrrules.
Require Import spectac iltac triple.
Require Import pecoff.

Require Import stringbuff.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.


(****************************************************************)
(* Compiler                                                     *)
(****************************************************************)

Section Compiler.

Variables (acc : DWORD)(rej : DWORD)(err : DWORD).

Variables
  (dfa_size: nat)
  (dfa_init: 'I_dfa_size)
  (alphabet: list DWORD)
  (accept: 'I_dfa_size -> bool)
  (trans: 'I_dfa_size -> DWORD -> 'I_dfa_size).

Definition dfa_state := 'I_dfa_size.

Variables (loBuff hiBuff: DWORD).
Variable (str: seq DWORD).


Definition run (k: DWORD) := safe @ (EIP ~= k).
Hint Unfold run: specapply.


(*
 * Computation: jumpNext
 *)
  
Section JumpNext.

Variables (c: DWORD)
          (next: DWORD).

Definition jumpNext : program :=
  CMP EBX, c ;;
  JE next.

Lemma jumpNext_block 
        (i j: DWORD)(pd v : DWORD) :

 |-- (|> run next @ (v == c /\\ empSP)
  //\\   run j @ (v != c /\\ empSP)
 (* --------------------------------------- *)  -->> 
        run i)

 (* Memory: *)
      @ (EAX ~= pd ** EBX ~= v)
      @ OSZCP_Any

 (* Program: *)
     <@ (i -- j :-> jumpNext).
Proof.
  rewrite /jumpNext/run.
  unfold_program; specintros=> i1.

  (* RUN: CMP EBX, c *)
  specapply CMP_RI_eq_rule; first by sbazooka.

  (* RUN: JE next *)
  specapply JZ_rule; first by sbazooka.
  rewrite <-spec_reads_frame.
  autorewrite with push_at.
  apply limplValid; apply landR.
  
    * (* FLOW: run [next] *)
    apply landL1.
    do 2 cancel1.
    sdestruct=> /eqP ->.
    rewrite /OSZCP_Any/flagAny.
    by sbazooka.

    * (* FLOW: run [j] *)
    apply landL2.
    cancel1. 
    sdestruct=> /eqP ->.
    rewrite /OSZCP_Any/flagAny.
    by sbazooka.
Qed.


End JumpNext.


(*
 * Computation: jumpTable
 *)

Section JumpTable.

Variables (labels:  dfa_size.-tuple DWORD)
          (s : dfa_state).

Definition jumpTable :=
    foldr prog_seq prog_skip 
          [seq jumpNext c (tnth labels (trans s c))
          | c <- alphabet].

Lemma jumpTable_block
        (i j: DWORD)(pd: DWORD)(v: DWORD) : 

 |-- ( (|>  Forall k: 'I_dfa_size, 
        run (tnth labels k) 
            @ ((v \in alphabet)
            && (trans s v == k)
            /\\ empSP ))
    //\\ (run j @ (v \notin alphabet /\\ empSP))
 (* ------------------------------------------------ *) -->> 
    run i)

 (* Memory: *)
      @ (EAX ~= pd ** EBX ~= v ** OSZCP_Any)

 (* Program: *)
     <@ (i -- j :-> jumpTable).
Proof.
  (* TODO: simplify proof *)

  rewrite /jumpTable/run.
  move: i j.
  elim: alphabet=> [i j |a l IH i j] //=.
  * (* CASE: alphabet = [::] *)
    rewrite /memIs /=; specintros=> <-.
    rewrite <-spec_reads_frame.
    rewrite <-spec_frame.
    apply limplValid; apply landL2.
    autorewrite with push_at; cancel1.
    by sbazooka.
  * (* CASE: alphabet = a :: l *)
    unfold_program; specintros=> jumpTable.

    (* RUN: jumpNext a (tnth labels (next a)) *)
    specapply jumpNext_block; first by ssimpl.
    specsplit.

    - (* CASE: v == a: run [tnth labels (next a)] *)
      rewrite <-spec_reads_frame; autorewrite with push_at.
      apply limplValid; apply landL1.
      rewrite ->spec_later_forall.
      apply lforallL with (x := trans s a).
      autorewrite with push_at.
      do 3 cancel1; sdestruct=> /eqP ->.
      sbazooka.
      apply/andP; split; last by done.
      by apply mem_head.

    - (* CASE: v == a: run [jumpTable] *)      
      autorewrite with push_at.
      specintros=> neqva.
      specapply IH; first by sbazooka.
      clear IH.
      specsplit;
        rewrite <-spec_reads_frame;
        rewrite ->spec_at_emp;
        apply limplValid.
      + (* CASE: Forall k, |>safe @ (EIP~=tnth labels k) *)
        apply landL1.
        autorewrite with push_at.
        cancel1.
        apply lforallR=> k.
        apply lforallL with (x := k).
        cancel2. cancel1.
        lpropandL=> /andP [q1 q2].
        lpropandR; first by sbazooka.
        apply /andP; split; last by exact: q2.
        rewrite in_cons.
        apply/orP.
        by exact: (or_intror q1).
                
      + (* CASE: |>safe @ (EIP~=exit) //\\ safe @ (EIP~=j) *)
        apply landL2.
        autorewrite with push_at; cancel1.
        sdestruct=> q.
        sbazooka.
        rewrite in_cons; rewrite negb_or.
        apply/andP; split; exact.
Qed.


End JumpTable.


Section NextChar.

Variables (labels : dfa_size.-tuple DWORD)
          (s: dfa_state)
          (exit: DWORD).

Definition nextChar: program :=
    (* Move pointer to next character *)
    MOV EBX, [EAX] ;;
    ADD EAX, (#4 : DWORD) ;;
    (* Exit if end of string: *)
    jumpNext #0 exit.

Lemma nextChar_block
        (i j: DWORD)(pd: DWORD)(l1 l2: seq DWORD)(l1_string: CString l1) :

  |-- (run exit @ ((l2 == [::])
               /\\ EAX ~= hiBuff +# 4
                ** EBX?
                ** loBuff -S- hiBuff :-S> l1)
  //\\ run j @ (Exists c: DWORD,
                Exists l2': seq DWORD,
                (l2 == [:: c & l2' ])
             && (c != #0)
            /\\ EAX ~= pd +# 4
             ** EBX ~= c
             ** (loBuff -- next (pd +# 3) :-> (cat l1 [:: c]))
             ** (next (pd +# 3) -S- hiBuff :-S> l2'))
(* -------------------------------------*) -->>
   run i @ (EAX ~= pd
         ** EBX?
         ** loBuff -- pd :-> l1 
         ** pd -S- hiBuff :-S> l2))

  (* Memory: *)
     @ OSZCP_Any

  (* Program: *)
    <@ (i -- j :-> nextChar).
Proof.
  rewrite /nextChar/run. 
  unfold_program; specintros=> add jumpNext.
  
  case: l2=> [|c l2].

  * (* CASE: l2 = [::] *)
    rewrite ->caseString_nil.
    specintros=> eq_pd.

    (* RUN: MOV EBX, [EAX] *)
    specapply MOV_RM_rule;
      first by sbazooka;
               rewrite addB0;
               move/eqP: eq_pd ->;
               sbazooka.

    (* RUN: ADD EAX, 4 *)
    specapply ADD_RI_ruleNoFlags; first by sbazooka.
   
    
    (* jumpNext #0 exit *)
    specapply jumpNext_block; first by rewrite /regAny; sbazooka.
 
    specsplit;
      rewrite <-spec_reads_frame; autorewrite with push_at;
      apply limplValid.
   

    - (* CASE: end of string: run exit *)    
      apply landL1; rewrite <-spec_later_weaken; 
        cancel1; sdestruct=> _;
        rewrite addB0; rewrite /regAny; 
        move/eqP: eq_pd=> ->;
        sbazooka.
      rewrite ->(emptyString l1_string).
      by reflexivity.

    - (* CASE: impossible: got a non zero at the end of string! *)
      apply landL2.
      cancel1.
      by sdestruct=> /eqP //.

  * (* CASE: l2 =~ [:: c & cs ] *) 
    rewrite ->caseString_cons.
    specintros=> c_neq_0.

    (* MOV EBX, [EAX] *)
    specapply MOV_RM_rule;
      first by sbazooka;
               rewrite addB0;
               sbazooka.

    (* ADD EAX, 4 *)
    specapply ADD_RI_ruleNoFlags; first by sbazooka.

    (* jumpNext #0 exit *)
    specapply jumpNext_block; first by sbazooka.

    specsplit;
      rewrite <-spec_reads_frame; autorewrite with push_at;
      apply limplValid.

    - (* CASE: impossible: end of string *)
      apply landL1.
      rewrite <-spec_later_weaken; do 2 cancel1.
      sdestruct=> /eqP c_eq_0.
      by rewrite c_eq_0 // in c_neq_0.

    - (* CASE: run [j] *)
      apply landL2.
      cancel1; rewrite /regAny.
      have: CString (l1 ++ [:: c]) by apply: snocCString.
      move=> string_l1c.
      ssimpl; rewrite [pd +# 0] addB0; sdestruct=> _.
      rewrite ->empSPL; rewrite ->sepSPC1; rewrite <-sepSPA.
      sbazooka; first by apply/andP; split; exact.
      rewrite seqMemIs_cat. rewrite {2}/memIs/pairMemIs /fst/snd. 

      sbazooka. rewrite /pointsTo. sdestruct => q'. rewrite -> memIsDWORD_rangeGen. sdestruct => H. 
      rewrite -H. setoid_rewrite ->seqMemIs_cons. sbazooka.  ssimpl. rewrite seqMemIs_nil. sbazooka. 
Qed.

End NextChar.

(*
 * Computation: transitionState
 *)

Fixpoint lang
           (s: dfa_state)
           (w: seq DWORD): bool := 
  match w with 
    | [::] => accept s
    | [:: a & w] => (a \in alphabet) && lang (trans s a) w
  end.

Definition runAccept 
             (labels: dfa_size.-tuple DWORD)
             (s: dfa_state) :=
  run (tnth labels s)
        @ (Exists pd: DWORD,
           Exists l1: seq DWORD,
           Exists l2: seq DWORD,
           (CString l1)
        && (str == (cat l1 l2))
        && (lang s l2 == lang dfa_init str)
       /\\ (EAX ~= pd)
        ** EBX?
        ** (loBuff -- pd :-> l1)
        ** (pd -S- hiBuff :-S> l2)).
Hint Unfold runAccept : specapply.

Definition runAccepts 
             (labels: dfa_size.-tuple DWORD): spec :=
  Forall k: 'I_dfa_size, runAccept labels k.
Hint Unfold runAccepts : specapply.

Definition runAcc :=
  run acc
      @ (lang dfa_init str
     /\\ EAX ~= hiBuff +# 4 
      ** EBX? 
      ** loBuff -S- hiBuff :-S> str).
Hint Unfold runAcc: specapply.

Definition runRej :=
  run rej
      @ ((~~ (lang dfa_init str))
     /\\ EAX ~= hiBuff +# 4 
      ** EBX? 
      ** loBuff -S- hiBuff :-S> str).
Hint Unfold runRej: specapply.

Definition runErr :=
  run err
        @ (Exists l1: seq DWORD,
           Exists v: DWORD,
           Exists l2: seq DWORD,
           (str == (cat l1 [:: v & l2]))
        && (v \notin alphabet)
       /\\ EAX?
        ** EBX?
        ** (loBuff -S- hiBuff :-S> str)).
Hint Unfold runErr: specapply.

Definition Post :=
           runAcc
      //\\ runRej
      //\\ runErr.

Section TransitionState.

Variables (labels : dfa_size.-tuple DWORD)
          (s: dfa_state).

Definition transitionState : program :=
  (tnth labels s):;;
    (* Increment but stay inside buffer *)
    nextChar (match accept s with
                | true => acc 
                | false => rej
              end);;
    (* Jump table: *)
    jumpTable labels s ;;
    (* Char not in alphabet: *)
    JMP err.


Lemma transitionState_block 
        (i j: DWORD) :

  |--    (|> runAccepts labels
      //\\ Post
   (* -------------------------------------------- *) -->>
      runAccept labels s)

   (* Memory: *)
     @ OSZCP_Any

   (* Program: *)
     <@ (i -- j :-> transitionState).
Proof.
  rewrite /transitionState/Post.
  unfold_program.
  specintros=> _ <- -> jmpTable jumpErr.
  rewrite /runAccept/run.
  specintros=> pd l1 l2 /andP [/andP [l1_cstring eql1l2str] accl2str].

  (* Get nextChar *)
  specapply nextChar_block; 
    [ by sbazooka 
    |
    | by exact: l1_cstring].
  specsplit.

  - (* CASE: end of string *)

    (* RUN: [if accept s then acc else rej] *)
    specintros=> /eqP l2nil.
    rewrite l2nil {1}/lang in accl2str.
    case: (accept s) accl2str => accl2str;
      rewrite <-spec_reads_frame;
      autorewrite with push_at;
      apply limplValid; apply landL2.

      + (* CASE: accepting state *)
        apply landL1.
        rewrite /runAcc/run;
          autorewrite with push_at; 
          cancel1; sbazooka.
        rewrite l2nil cats0 in eql1l2str.
        by move/eqP: eql1l2str=> ->.

      + (* CASE: rejecting state *)
        apply landL2; apply landL1.
        rewrite /runRej/run;
          autorewrite with push_at; 
          cancel1; sbazooka.
        rewrite l2nil in eql1l2str.
        move/eqP: eql1l2str=> ->.
        by rewrite cats0.

  - (* CASE: non empty string *)

    (* RUN: jumpTable labels s *)
    specintros=> c l2' /andP[[/eqP eql2cl2'] c_not_0] .
    specapply jumpTable_block; first by sbazooka.
    specsplit.

    * (* CASE: c matched a rule *)

      (* RUN: state k *)
      rewrite <-spec_reads_frame; autorewrite with push_at.
      apply limplValid; apply landL1.
      rewrite ->spec_later_forall.
      rewrite /runAccepts. 
      specintros=> k; cancel1; 
        autorewrite with push_at;
        apply lforallL with (x := k).
      rewrite /runAccept/run.
      autorewrite with push_at.
      do 2 cancel1; rewrite /regAny.
      sdestruct => /andP [c_in_alphabet transc].
      sbazooka.
      do 2 try (apply/andP; split).

      - (* CString (l1 ++ [:: c]) *)
        apply snocCString. apply l1_cstring. apply c_not_0. rewrite eql2cl2' in eql1l2str. rewrite -(catA l1 _ l2'). assumption. 
      - (* lang k l2' == lang dfa_init str *)
        move/eqP: accl2str=> <-.
        rewrite eql2cl2'. 
        simpl. rewrite c_in_alphabet (eqP transc) andTb. done. 

        *  (* CASE: c \notin alphabet *)
      rewrite /pointsToS. 
      rewrite -> (@readerSeqMemIs_nonHwm _ _ l2' (next (pd +# 3)) hiBuff). 
      sdestruct => CS. sdestruct => d. sdestruct => EQ. rewrite EQ.  apply nextIsInc in EQ. rewrite -addB_addn in EQ. 
      rewrite EQ. sbazooka. 

      (* RUN: JMP err *)
      specintros=> c_notin_alphabet.
      specapply JMP_I_rule; first by sbazooka.

      (* RUN: [err] *)
      rewrite /runErr/run.
      rewrite <-spec_reads_frame; autorewrite with push_at.
      apply limplValid; do 3 apply landL2.
      rewrite <-spec_later_weaken; cancel1; rewrite /regAny.

      have: (cat (cat l1 [:: c]) l2') = str
        by move/eqP: eql1l2str=> ->;
           rewrite eql2cl2';
           rewrite cats1 cat_rcons.
      move=> eql1cl2'.

      sbazooka.
      - (* CASE: str = l1 ++ c :: l2'  and c \notin alphabet *)
        apply/andP; split; 
        by [ rewrite -eql1cl2' cats1 cat_rcons
           | exact: c_notin_alphabet ].

      - (* CASE: splitting of str *)
      rewrite /pointsToS. 
      rewrite -> (@readerSeqMemIs_nonHwm _ _ l2' (next (pd +# 3)) hiBuff). 
      sdestruct => CS. sdestruct => d. sdestruct => EQ. rewrite EQ.  apply nextIsInc in EQ. rewrite -addB_addn in EQ.
      replace (3+1) with 4 in EQ by done. rewrite -EQ {EQ}.
      sbazooka. rewrite -eql1cl2'. apply catCString => //. apply snocCString => //. 
      rewrite -eql1cl2' !seqMemIs_cat. rewrite {3}/memIs/pairMemIs/fst/snd. 
      apply lexistsR with (pd+#4). rewrite !seqMemIs_cat. sbazooka. reflexivity. 
Qed.       

End TransitionState.


Section ConcatStates.

(* Program memory (unfolded) *)

Definition ordS n (k: 'I_n) : 'I_(n.+1) := lift ord0 k.

(*
Compute (ord0 : 'I_4).
Compute (val (ordS ord0 : 'I_4)).
Compute (val (ordS (ordS ord0) : 'I_4)).
*)
 
Lemma ord_ind (P : forall n, 'I_n -> Prop) : 
  (forall n, P n.+1 ord0) -> 
  (forall n, forall k, P n k -> P n.+1 (ordS k)) -> 
  forall n k,
  P n k.
Proof.
move=> bc ih.
elim=> [[m lemn]|n IHn [m lemn]];
  first by discriminate lemn.
case: m lemn=> [le0n|m lesmsn].
  (* P n.+1 ord0 *)
  have: Ordinal le0n = ord0 by exact: ord_inj.
  move=> ->; exact: bc.

  (* P n.+1 (ordS k) *)
  set k: 'I_n := @Ordinal n m lesmsn.
  have: Ordinal lesmsn = ordS k by exact: ord_inj.
  move=> ->.
  apply ih; apply IHn; by exact.
Qed.

Fixpoint nat_ind (P : nat -> Type)
                   (bc : P 0)
                   (ih : forall n, P n -> P n.+1)
                   (n: nat) : P n :=
  match n with
    | 0 => bc
    | n.+1 => ih n (nat_ind bc ih n)
  end.

Definition PMem n  : ('I_n -> SPred) -> SPred :=
  @nat_ind (fun n => ('I_n -> SPred) -> SPred)
          (fun _ => empSP)
          (fun n IH pmem => pmem ord0 ** IH (fun k => pmem (ordS k)))
          n.

(*
Fixpoint PMem n : ('I_n -> SPred) -> SPred :=
  match n as n' return ('I_n' -> SPred) -> SPred with
    | 0 => fun pmem => empSP
    | n.+1 => fun pmem => pmem ord0 ** PMem (fun k => pmem (ordS k))
  end.
*)


Lemma concatStates_logic
        (P: 'I_dfa_size -> spec) Mem :

    (forall s: 'I_dfa_size, |-- P s <@ Mem s)
 (* ------------------------------------------------------ *)->
    forall s: 'I_dfa_size, |-- P s <@ PMem Mem.

Proof.
  clear dfa_init accept trans.
  move=> H s.
  rewrite /PMem/nat_ind.
  induction s using ord_ind; rewrite /=.
  * (* CASE: s ~= ord0 *)
    rewrite <-spec_reads_merge.
    rewrite <-spec_reads_frame.
    by exact: H.
  * (* CASE: s ~= ordS s *)
    rewrite ->sepSPC1.
    rewrite <-spec_reads_merge.
    rewrite <-spec_reads_frame.
    apply (IHs (fun k => P (ordS k))) => s'.
    by exact: H.
Qed.

Variables (labels: dfa_size.-tuple DWORD).
  
Definition concatStates :=
  PMem (fun s => Exists i: DWORD, Exists j: DWORD,
          i -- j :-> transitionState labels s).

Lemma transitionState_addr s (i j: DWORD) : 
     i -- j :-> transitionState labels s
 |-- i = tnth labels s /\\ i -- j :-> transitionState labels s.
Proof.
  rewrite /transitionState.
  unfold_program.
  sdestructs=> _ <- -> k l.
  sbazooka.
  rewrite {4}/memIs/=.
  apply lexistsR with (x := tnth labels s).
  rewrite {4}/memIs/=.
  sbazooka.
  rewrite {4}/memIs/=.
  apply lexistsR with (x := k).
  rewrite {5}/memIs/=.
  sbazooka.
  reflexivity.
Qed.

(*
  |--    ((Forall k: 'I_dfa_size, |> runAccept labels k)
      //\\ runExit acc
      //\\ runExit rej
      //\\ runErr 
   (* -------------------------------------------- *) -->>
      runAccept labels s)
*)             
Lemma concatStates_block
          (s: 'I_dfa_size) :

    |-- ((|> runAccepts labels)
       //\\ Post
 (* ------------------------------------------------*) -->> 
       runAccept labels s)
       
 (* Memory: *)
     @ OSZCP_Any

 (* Program: *)
    <@ concatStates.
Proof.
  move: s.
  apply concatStates_logic=> s.
  specintro=> j.
  rewrite /runAccept/run.
  specintros=> k l c str' q;
    rewrite ->transitionState_addr;
    specintros=> ->.
  specapply transitionState_block; 
    first by sbazooka.
  by rewrite /runAccepts/runAccept/run;
     rewrite <-spec_reads_frame;
     rewrite ->spec_at_emp;
     apply limplAdj;
     apply landL2.
Qed.

End ConcatStates.

(* Don't need to quantify over F and Mem, 
   frame that in proof*)
Lemma concatRuns_logic
        {S} Q (P: S -> spec) F Mem :

    (forall s, |-- (Q -->> P s) @ F <@ Mem)
 (* ------------------------------------------------------ *)->
    |-- (Q -->> Forall s, P s) @ F <@ Mem.

Proof.
  move=> H.
  specintros=> s.
  move: H => /(_ s) H.
  exact: H.
Qed.


Section ConcatRuns.

Variables (labels: dfa_size.-tuple DWORD).

Lemma concatRuns_block :

    |-- ((|> runAccepts labels)
       //\\ Post
 (* ------------------------------------------------*)
       -->> runAccepts labels)
       
 (* Memory: *)
     @ OSZCP_Any

 (* Program: *)
    <@ (concatStates labels).

Proof.
  apply concatRuns_logic=> s.
  apply concatStates_block.
Qed.

End ConcatRuns.

Section LobRuns.

Variables (labels: dfa_size.-tuple DWORD).

Lemma spec_lob_impl C S P :
       C |-- |> P //\\ S -->> P ->
       C |-- S -->> P.
Proof.
  move=> H.
  apply limplAdj.
  apply spec_lob_context.
  rewrite ->landA.
  rewrite [S //\\ |> P]landC.
  apply landAdj.
  exact: H.
Qed.

Lemma lobRuns_block :

    |-- (Post 
 (* ------------------------------------------------*) -->>
         runAccepts labels)
       
 (* Memory: *)
     @  OSZCP_Any
 (* Program: *)
    <@ (concatStates labels).

Proof.
  etransitivity; 
    first by apply concatRuns_block.
  cancel2; last by reflexivity.
  cancel2.
  apply spec_lob_impl; reflexivity.
Qed.


End LobRuns.


(*
 * 
 *)

Section CompileDFA.

Variables (labels: dfa_size.-tuple DWORD).

Definition dfaProg n : ('I_n -> program) -> program :=
  @nat_ind (fun n => ('I_n -> program) -> program)
           (fun _ => prog_skip)
           (fun n IHn compileState => compileState ord0 ;;
                                      IHn (fun k => compileState (ordS k)))
           n.

(* Write as a fold *)
(*
Fixpoint dfaProg n : ('I_n -> program) -> program :=
  match n as n' return ('I_n' -> program) -> program with
    | 0 => fun compileState => prog_skip
    | n.+1 => fun compileState => compileState ord0 ;; 
                                 (dfaProg (fun k => compileState (ordS k)))
  end.
*)

Lemma compileDFA_abstract n (P : 'I_n -> program)(i j: DWORD) :
   i -- j :-> dfaProg P
   |-- PMem (fun s => Exists i: DWORD, Exists j: DWORD,
                        i -- j :-> P s).
Proof.
  rewrite /dfaProg/PMem.
  elim: n i j P=> [i j P | n IHn i j P] //=.
  * (* CASE: n ~= 0 *)
    rewrite /memIs/=.
    sdestruct=> _.
    sbazooka.
  * (* CASE: n ~= n.+1 *)
    unfold_program.
    sdestruct=> i'.
    sbazooka.
Qed.

Definition compileDFA (labels: dfa_size.-tuple DWORD): program :=
  dfaProg (transitionState labels).

Lemma compileDFA_logic (i j: DWORD):  

  i -- j :-> compileDFA labels |-- concatStates labels.
Proof.
  
  rewrite /compileDFA/concatStates/dfaProg/PMem.
  apply: compileDFA_abstract.
Qed.

Lemma seqStates_block
          (i j: DWORD) :

    |-- (Post
 (* ------------------------------------------------*) -->> 
         runAccepts labels)
       
 (* Memory: *)
     @ OSZCP_Any

 (* Program: *)
    <@ (i -- j :-> compileDFA labels).

Proof.  
  rewrite ->compileDFA_logic. 
  apply lobRuns_block.
Qed.


End CompileDFA.

(*
 * Computation: startDFA
 *)

Section StartDFA.

Variables
  (labels: dfa_size.-tuple DWORD).

Definition start: program :=
  JMP (tnth labels dfa_init);;
  compileDFA labels.

Lemma interpolation P Q R S:
  R |-- P -> Q |-- S ->
  (P -->> Q) |-- (R -->> S).
Proof.
  move=> H1 H2.
  apply limplAdj.
  rewrite ->H1.
  apply limplL; first by done.
  rewrite <-H2; apply landL1.
  done.
Qed.

Lemma start_block 
        (i j: DWORD):

    |-- (((run acc @ (lang dfa_init str
                  /\\ EAX?))
    //\\ (run rej @ (~~ (lang dfa_init str)
                  /\\ EAX?))
    //\\ (run err
        @ (Exists l1: seq DWORD,
           Exists v: DWORD,
           Exists l2: seq DWORD,
           (str == (cat l1 [:: v & l2]))
        && (v \notin alphabet)
       /\\ EAX?)))
 (* ------------------------------------------------*) -->> 
         run i @ (EAX ~= loBuff))
       
 (* Memory: *)
     @ OSZCP_Any
     @ EBX?
     @ (loBuff -S- hiBuff :-S> str)

 (* Program: *)
    <@ (i -- j :-> start).

Proof.
  rewrite /start/run.
  unfold_program; specintros=> codeDFA.

  (* Run: JMP (tnth labels dfa_init *)
  specapply JMP_I_rule; first by sbazooka.
  rewrite <-spec_later_weaken.

  (* Apply: correctness of compileDFA *)
  
  rewrite [(_ -- _ :-> _) **( _ -- _:-> _)]sepSPC.
  rewrite <-spec_reads_merge.
  rewrite <-spec_reads_frame.
  etransitivity; first by apply seqStates_block.
  (* Delete read frame *)
  cancel2; last by reflexivity.
  (* Delete frame *)
  autorewrite with push_at.

  apply interpolation.
    rewrite /Post/runAcc/runRej/regAny/run.
    specsplit.

      apply landL1.
      autorewrite with push_at; cancel1.
      sdestruct=> q; ssplit; first by exact.
      sbazooka.

      specsplit.
      apply landL2. apply landL1.
      autorewrite with push_at; cancel1.
      sbazooka.

      apply landL2; apply landL2.
      rewrite /runErr/run/regAny.
      autorewrite with push_at.
      cancel1.
      sdestructs=> l1 v l2 q pd v2.
      sbazooka.
      exact q.

    rewrite /runAccepts/runAccept/run/regAny.
    autorewrite with push_at.
    apply lforallL with (x := dfa_init).
    autorewrite with push_at.
    cancel1.
    sdestruct=> v.
    ssimpl.
    apply lexistsR with (x := loBuff).
    apply lexistsR with (x := [::]).
    apply lexistsR with (x := str).
    sbazooka.
    do 2 try (apply/andP; split); done.
    rewrite seqMemIs_nil.
    sbazooka.
Qed.

End StartDFA.

Fixpoint mkLabelsHelp
           (n : nat) : (n.-tuple DWORD -> program) -> program :=
  match n with
    | 0 => fun g => g [tuple]
    | n.+1 => fun g => prog_declabel None (fun a => 
                       mkLabelsHelp (fun ls =>
                       g [tuple of a :: ls]))
  end.

Definition mkLabels
             (body: dfa_size.-tuple DWORD -> program) 
           : program :=
  mkLabelsHelp (fun ls => body ls).

Definition compiler : program :=
  mkLabels (fun labels => start labels).

End Compiler.

