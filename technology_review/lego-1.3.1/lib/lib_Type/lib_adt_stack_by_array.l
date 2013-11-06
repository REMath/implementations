(***********************************)
(* LEGO Summerschool August 1995   *)
(* Hetzelsdorf                     *)
(* Author: Zhaohui Luo             *)
(* Email: Zhaohui.Luo@durham.ac.uk *)
(***********************************)

(******************************************************************)
(* Minor modifications to achieve compatibility with the official *)
(* library by Thomas Schreiber <tms@dcs.ed.ac.uk> on 24 May 1996  *)
(******************************************************************)

Module lib_adt_stack_by_array Import lib_nat_Lt lib_adt_stack lib_adt_array;

(**************************************************
****** Example: stacks implemented by arrays ******
**************************************************)

(*************************************
******* abstract implementation ******
*************************************)

(* refinement map refnSA: Str_ARRAY -> Str_STACK, constructed by proof *)
Goal refnSA : 
     ARRAY.Str -> STACK.Str;
Intros A; Refine make_Str_STACK;
Refine make_Setoid; 
(* domain of impl of stack: arr-ptr pairs *)
[domImpl = Prod A.Array.dom nat]; Refine domImpl;	
(* equality over the impl domain *)
[eqImpl [s,s':domImpl] =
       and (Eq s.sig_pi2 s'.sig_pi2) 
	   ({i:nat}(Lt i s.sig_pi2)->(Eq (A.access s.sig_pi1 i) (A.access s'.sig_pi1 i)))];	
Refine eqImpl;	
(* empty stack *)
[emptyImpl = Pr A.newarray zero : domImpl]; Refine emptyImpl;	
(* push *)
[pushImpl [n:nat][arri:domImpl] =
       Pr (A.assign n arri.sig_pi1 arri.sig_pi2) (suc arri.sig_pi2) : domImpl];
Refine pushImpl;
(* pop *)
[popImpl[arri:domImpl]= Pr arri.sig_pi1 (pred arri.sig_pi2) : domImpl]; Refine popImpl;	
(* top *)
[topImpl[ai:domImpl]= if_zero ai.sig_pi2 zero (A.access ai.sig_pi1 (pred ai.sig_pi2)) : nat];	
Refine topImpl;	
(* QED *)
Save;

(* refinement proof *)

(* Lemmas *)

[A:ARRAY.Str][ax_arrayA : ARRAY.Ax A];

Goal equivSTACK : 
     Equivalence (eq|A.refnSA.Stack);
intros; Refine pair3; 
(* reflexivity *)
Intros _; Refine pair; Refine Eq_refl; intros; Refine Eq_refl;
(* symmetry *)
Intros t u tu; Refine pair; 
Qrepl tu.fst; Refine Eq_refl;
intros; Refine Eq_sym; Refine tu.snd; Qrepl tu.fst; Try Immed;
(* transitivity *)
Intros t u v tu uv; Refine pair;
Qrepl tu.fst; Refine uv.fst;
intros; Refine Eq_trans; Refine A.access u.sig_pi1 i;
Refine tu.snd; Try Immed; Refine uv.snd; Qrepl Eq_sym tu.fst; Try Immed;
(* QED *)
Save; 

Goal axSTACK1 : 
     A.refnSA.AxSTACK1;
Expand AxSTACK1; Refine pair; 
Refine Eq_refl; 
intros; Refine not_n_Lt_zero i; Refine H;
(* QED *)
Save;

Goal axSTACK2 :
     A.refnSA.AxSTACK2;
Refine Eq_refl;
(* QED *)
Save;

(* lemma not in pub lib *)
Goal axSTACK3 : 
     A.refnSA.AxSTACK3;
Expand AxSTACK3; Refine ax_arrayA; Intros _ _ axA2;
intros; Refine pair; 
Refine Eq_refl;
intros; Refine axA2 n s.sig_pi2 i s.sig_pi1; intros; Refine H4;
Intros _; Refine Lt_not_Eq ? ? H2; Refine H5.Eq_sym;
(* QED *)
Save;

Goal axSTACK4 : 
     A.refnSA.AxSTACK4;
Expand AxSTACK4; Refine ax_arrayA; Intros _ _ axA2; 
intros; Refine axA2 n s.sig_pi2 s.sig_pi2 s.sig_pi1; 
intros; Refine H2; Refine Eq_refl;
(* QED *)
Save;

Discharge A;


(* correctness proof of the abstract implementation *)

Goal refnSA.Sat; 
Intros A ax_arrayA; Refine pair5;
(* Refine pair; *)
Refine equivSTACK;
(* Refine respSTACK ax_arrayA; *)
Refine axSTACK1;
Refine axSTACK2;
Refine axSTACK3 A ax_arrayA;
Refine axSTACK4 A ax_arrayA;
(* QED *)
Save sat_refnSA;


(******** Notes on observational equivalence *************************
The associated explicit equivalence relation (in Setoid) represents
"observational equivalence" among realisations.  If one instead used
an internal equality such as the Leibniz equality, the above refnSA is
not a correct refinement.  In the above, stack/array-equalities are
only specified to be equivalence relations.  Usually, a stronger
requirement would be congruence, and the following shows that, if so,
refnSA is still a correct implementation, as shown in [Luo93].
**********************************************************************)

