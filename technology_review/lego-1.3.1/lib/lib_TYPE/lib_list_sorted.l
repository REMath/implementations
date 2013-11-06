(* Author: James McKinna <jhm@dcs.ed.ac.uk> *)

(* CHANGES

   26 Jan 1996
   Thomas Schreiber <tms@dcs.ed.ac.uk>
   converted LEGO file to library compatible module for arbitray equality relation*)

Module lib_list_sorted Import lib_list_PermII;

[A|Type];

(*** temporary section ***)
[l|list A];
Goal lengthisahomomorphismcons : {n|nat}{eq:Eq (suc n) (length l)}Ex [a:A]Eq l (cons a (tail l));
Refine list_elim [l:list A]{n|nat}{eq:Eq (suc n) (length l)}Ex [a:A]Eq l (cons a (tail l));

  (** base case **)
  intros; Refine suc_not_zero; Expand is_suc;
  Refine ExIntro; Try Immed;

  (** step case **)
  intros;Refine ExIntro;Refine +1 Eq_refl;

Save lengthisahomomorphismcons;

Discharge l;
(*** end of temporary section ***)

[R:Rel A A]
[reflR:refl R]
[transR:trans R]
[antisymR:{a,b|A}((R a b)->(R b a)-> (Eq a b))];

(* here's the specification *)

[Rlist [B|Type][R:Rel A B][a:A] =
  list_rec trueProp ([b:B][_:list B][P:Prop]and (R a b) P)];

[Sorted       = list_rec trueProp 
                 ([a:A][l:list A][P:Prop]and (Rlist R a l) P) : Pred (list A)];

[SortSpec  = [l,m:list A]and (Sorted m) (Perm l m) : Rel (list A) (list A)];

(* and here is Rod's brilliantly clever induction principle *)

Goal sortedlistinduction : {B|Type}{phi:Rel (list A) B}{n|B}{c|A -> (list A) -> B -> B}
               (phi (nil A) n)
       ->
               ({a|A}{l|list A}{b|B}(Sorted(cons a l))  ->
                        (phi l b) -> phi (cons a l) (c a l b))
       ->
             {l:list A}(Sorted l) -> (phi l (list_rec n ([a:A][l:list A][b:B]c a l b) l));

intros;
Refine list_elim [l:list A](Sorted l) ->
         phi l (list_rec n ([a:A][l:list A][b:B]c a l b) l);

Try Immed;
intros;Try Immed;
intros;Refine H3;
intros;
Refine H1;Try Immed;
Refine x2_ih;Try Immed;

Save sortedlistinduction;

(* and some lemmas about the specification *)

Goal nilSorted : Sorted (nil A);
Intros;Try Immed;
Save nilSorted;

[b,c|A][m,n|list A];

Goal nilRlist : Rlist R c (nil A);
Intros;Try Immed;
Save nilRlist;

Goal heredSortedlemma : (Sorted (cons b n)) -> Sorted n ;
intros;Refine H;intros;Try Immed;
Save heredSortedlemma;

Goal SortedImpliesRlist : (Sorted (cons b n)) -> Rlist R b n;
intros;Refine H;intros;Try Immed;
Save SortedImpliesRlist;

Goal heredRlistlemma : (Rlist R c (cons b n)) -> (Rlist R c n);
intros;Refine H;intros;Try Immed;
Save heredRlistlemma;

DischargeKeep b;

Goal heredRlist1 : (Rlist R c (append m n)) -> (Rlist R c n);
Refine list_elim [m|list A](Rlist R c (append m n))->Rlist R c n;
intros;Try Immed;
intros;Refine x2_ih;Refine heredRlistlemma;Try Immed;
Save heredRlist1;

Goal heredRlist2 : (Rlist R c (append m n)) -> (Rlist R c m);
Refine list_elim [m|list A](Rlist R c (append m n))->Rlist R c m;
intros;Refine nilRlist;
intros;Refine H;
intros;Refine pair;Try Immed;Refine x2_ih;Try Immed;
Save heredRlist2;

Goal appclRlist : (Rlist R c m) -> (Rlist R c n)  -> Rlist R c (append m n);
intros;Refine list_elim [m:list A](Rlist R c m)->Rlist R c (append m n);Try Immed;
intros;Try Immed;
intros;Refine H2;intros;
Refine pair;Refine +1 x2_ih;Try Immed;
Save appclRlist;

DischargeKeep b;

Goal heredSorted : (Sorted (append m n)) -> (and (Sorted m) (Sorted n));
Refine list_elim [m|list A](Sorted (append m n))->and (Sorted m) (Sorted n);
intros;Refine pair;Refine nilSorted;Try Immed;
intros;Refine H;
intros;Refine x2_ih;Try Immed;
intros;Refine pair;Refine pair;Try Immed;
Refine heredRlist2;Try Immed;
Save heredSorted;

Goal RlistIsMonotone : (R c b) -> (Rlist R b m) -> Rlist R c m;
Refine list_elim [m|list A](R c b)->(Rlist R b m)->Rlist R c m;
intros;Refine nilRlist;
intros;Refine H1;
intros;Refine pair;Try Immed;
Refine transR;Try Immed;
Refine x2_ih;Try Immed;
Save RlistIsMonotone;

Goal PermPreservesRlist : (Perm m n) -> (Rlist R c m) -> (Rlist R c n);
Refine PermPredE (Rlist R c);
intros;Refine appclRlist;Refine heredRlist1;Refine +2 heredRlist2;Try Immed;
intros;Refine cons_ih;Refine H;intros;Refine pair;Refine +1 H3;Try Immed;
Save PermPreservesRlist;

DischargeKeep b;

Goal SortedPermsHaveRHeads : (Sorted (cons b m)) ->(Sorted (cons c n)) ->
                   (Perm (cons b m)(cons c n)) -> (R b c);
intros;Refine fst;Refine Rlist R b n;
Equiv Rlist R b (cons c n);
Refine PermPreservesRlist;Try Immed;
Refine pair;Refine reflR;
Refine SortedImpliesRlist;Try Immed;
Save SortedPermsHaveRHeads;

DischargeKeep b;

Goal SortedPermsHaveEqualHeads : (Sorted (cons b m)) ->(Sorted (cons c n)) ->
                   (Perm (cons b m)(cons c n)) -> (Eq b c);
intros;Refine antisymR;
Refine SortedPermsHaveRHeads;Try Immed;
Refine SortedPermsHaveRHeads;Try Immed;
Refine symPerm;Try Immed;
Save SortedPermsHaveEqualHeads;  (* !!! *)

Discharge b;

Goal SortedPermsAreEqual : {l,m|list A}{sortedl:Sorted l}{sortedm:Sorted m}{permlm:Perm l m}Eq l m;
Refine list_elim [l|list A]{m|list A}{sortedl:Sorted l}{sortedm:Sorted m}{permlm:Perm l m}Eq l m;
intros;Refine nilPerm;Try Immed;
intros;Refine lengthisahomomorphismcons;
       Refine -1 PermRespLength permlm;
intros c eq; Qrepl eq;Refine sortedl;
intros; 
Claim Eq x1 c; Qrepl ?-0;
  Refine Eq_resp;
  Refine x2_ih; Try Immed;
  Refine +1 heredPermlemma; Refine -1 symPerm;
  Refine +1 c; Next +1; Qrepl Eq_sym eq;
  Qrepl Eq_sym ?-0; Try Immed;
  Refine symPerm; Try Immed;
  Claim Sorted (cons c (tail m));
  Refine ?-0.snd;
  Refine SortedPermsHaveEqualHeads; 
    Refine +1 tail m; Try Immed;
    Qrepl Eq_sym eq; Try Immed;
    Qrepl Eq_sym eq; Try Immed;
    Qrepl Eq_sym eq; Try Immed;
  Save SortedPermsAreEqual;  (* !!! *)

Discharge A;

