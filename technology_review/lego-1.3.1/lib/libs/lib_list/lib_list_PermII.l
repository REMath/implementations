(* new permutations, with resolution of the heredity problem, Aug 22-28 1991 *)
(* Author: James McKinna <jhm@dcs.ed.ac.uk> *)

(* CHANGES

   Thomas Schreiber <tms@dcs.ed.ac.uk>
   converted LEGO file to library compatible module *)

Module lib_list_PermII Import lib_list_length lib_rel_closure;

[A|Type(0)];

(*** temporary section ***)
[insert [a:A][h,k:list A] = append h (cons a k)];
[a,b|A][h,k|list A];

Goal insertnil : {eq:Eq (insert a h k) (nil A)}absurd;
Refine list_elim [h:list A]{eq:Eq (insert a h k) (nil A)}absurd;
intros; Refine nil_not_cons; Refine -0 Eq_sym; Try Immed;
intros; Refine nil_not_cons; Refine -0 Eq_sym; Try Immed;
Save insertnil;

DischargeKeep h;

Goal insertsingleton : (Eq (insert a h k) (cons b (nil A))) -> and3 (Eq (nil A) h) (Eq a b) (Eq (nil A) k);
Refine list_elim [h:list A]
     (Eq (insert a h k) (cons b (nil A))) -> and3 (Eq (nil A) h) (Eq a b) (Eq (nil A) k);

intros; Refine cons_inj H; intros eqab eqknil;
Refine pair3;
  Refine Eq_refl;
  Try Immed;
  Refine Eq_sym eqknil;

intros; Refine cons_inj H; intros;
Refine insertnil; Try Immed;
Save insertsingleton;

Goal insertapp : {l,m:list A} (Eq (insert a h k) (append l m)) ->
or
({phi:Prop}({n:list A}(Eq (insert a h n) l) -> (Eq (append n m) k) -> phi) -> phi)
({phi:Prop}({n:list A}(Eq (append l n) h) -> (Eq (insert a n k) m) -> phi) -> phi);

Refine list_elim [h:list A]{k,l,m:list A} (Eq (insert a h k) (append l m)) ->
or
({phi:Prop}({n:list A}(Eq (insert a h n) l) -> (Eq (append n m) k) -> phi) -> phi)
({phi:Prop}({n:list A}(Eq (append l n) h) -> (Eq (insert a n k) m) -> phi) -> phi);

Intros __;
Refine list_elim [l:list A]{k,m:list A}(Eq (insert a (nil A) k) (append l m))->
or
({phi:Prop}({n:list A}(Eq (insert a (nil A) n) l)->(Eq (append n m) k)->phi)->phi)
({phi:Prop}({n:list A}(Eq (append l n) (nil A))->(Eq (insert a n k) m)->phi)->phi);

intros;Refine inr;intros;Refine H1;Try Immed;Refine Eq_refl;

intros b1; intros;Refine inl; intros; 
Refine cons_inj H;
  intros aeqb1;
  Equiv (Eq k2 (append ??))->phi;
  intros decomp;
  Refine H1;
  Next -1; Qrepl aeqb1; Refine Eq_refl;
  Refine Eq_sym decomp;

intros b1 k1; intros;
Refine list_elim [l:list A]{m:list A}(Eq (insert a (cons b1 k1) k2) (append l m))->
or
({phi:Prop}({n:list A}(Eq (insert a (cons b1 k1) n) l)->(Eq (append n m) k2)->phi)->phi)
({phi:Prop}({n:list A}(Eq (append l n) (cons b1 k1))->(Eq (insert a n k2) m)->phi)->phi);

intros;Refine inr;intros;Refine H2;Refine +1 Eq_refl;Try Immed;

intros b2 k3; intros;

Refine cons_inj H1;
  intros b1eqb2 decomp;

Refine x2_ih; Try Immed;

intros;Refine inl;Refine H2;intros;Refine H5;Try Immed;
Qrepl b1eqb2; Refine Eq_resp (cons ?); Try Immed;

intros;Refine inr;Refine H2;intros;Refine H5;Try Immed;
Qrepl b1eqb2; Refine Eq_resp (cons ?); Try Immed; Try Immed;
Save insertapp;

Goal inseqins : {l,m|list A} (Eq (insert a h k) (insert a l m) ) ->
or
({phi:Prop}({n:list A}(Eq (insert a h n) l) -> (Eq (insert a n m) k) -> phi) -> phi)
(or
 (and (Eq l h) (Eq k m))
 ({phi:Prop}({n:list A}(Eq (insert a l n) h) -> (Eq (insert a n k) m) -> phi) -> phi));

intros;Refine insertapp l (cons a m);Try Immed;
intros;Refine H1;intros;Refine inl;intros;Refine H4;Try Immed;

intros;Refine H1;

Refine list_elim [n:list A](Eq (append l n) h)->(Eq (insert a n k) (cons a m))->
or
({phi:Prop}({n:list A}(Eq (insert a h n) l)->(Eq (insert a n m) k)->phi)->phi) 
(or 
 (and (Eq l h) (Eq k m))
 ({phi:Prop}({n:list A}(Eq (insert a l n) h)->(Eq (insert a n k) m)->phi)->phi));



intros;Refine inr;Refine inl;andI;
Refine Eq_trans; Refine +1 Eq_sym; Refine +1 append_nil; Try Immed;
Refine cons_inj H3; intros; Try Immed;

intros b1 k1; intros; Refine inr;Refine inr;intros;
Refine cons_inj H3; intros b1eqa decomp;
Refine H4;
Next +1; Qrepl Eq_sym b1eqa; Try Immed;

Save inseqins;
Discharge a;
(*** end of temporary section ***)


[swap [S:Rel (list A) (list A)] = {l,m:list A}S (append l m) (append m l)];

[conscl [a:A][S:Rel (list A) (list A)] = [m,n:list A]S (cons a m) (cons a n)];
[consClosed [S:Rel (list A) (list A)] = {a:A}(SubRel S (conscl a S))];

Goal iclSwap : IntersectionClosed swap;
Intros;Refine GsubF;Try Immed;
Save iclSwap;

Goal iclConscl : IntersectionClosed consClosed;
Intros;Refine GsubF;Try Immed;Refine hyp;Try Immed;
Save iclConscl;

[Fbase = andPred swap consClosed];

Goal iclBase : IntersectionClosed Fbase;
Refine iclAnd;Refine iclSwap;Refine iclConscl;
Save iclBase;

[PermBase = intersectionRel Fbase];
[swapBase = fst (intFhasF Fbase iclBase):swap PermBase];
[consclBase = snd (intFhasF Fbase iclBase):consClosed PermBase];

[Perm = closure (equiv|(list A)) PermBase];

Goal equivPerm : equiv Perm;
Refine closureI;Refine iclEquiv;
Save equivPerm;

[reflPerm = fst equivPerm:refl Perm];
[symPerm = fst(snd equivPerm):sym Perm];
[transPerm = snd(snd equivPerm):trans Perm];

Goal SubRel (Eq|(list A)) Perm;
Intros;Qrepl hyp;Refine reflPerm;Try Immed;
Save reflPerm';

Goal swapPerm : swap Perm;
Intros;Refine FR;intros;Refine H1;Refine swapBase;
Save swapPerm;

Goal consclPerm : consClosed Perm;
Intros _;
Refine closureE;
andI;Intros l;Refine reflPerm;
andI;Intros l m symhyp;Refine symPerm;Try Immed;
     Intros l m n lthyp rthyp;Refine transPerm;Try Immed;
Intros l m hyp;Refine closureInc;Refine consclBase;Try Immed;
Save consclPerm;

[appcl [l:list A][S:Rel (list A) (list A)] = [m,n:list A]
                                              S (append l m) (append l n)];
[appClosed [S:Rel (list A)(list A)] = {l:list A}(SubRel S (appcl l S))];

Goal iclAppcl : IntersectionClosed appClosed;
Intros;Refine GsubF;Try Immed;Refine hyp;Try Immed;
Save iclAppcl;

Goal appclPerm : appClosed Perm;
Refine list_elim [l:list A](SubRel Perm (appcl l Perm));
Intros ___;Try Immed;
intros;Intros ___;Refine consclPerm;Refine x2_ih;Try Immed;
Save appclPerm;

Goal recPerm : {l,m:list A}{perm_hyp:Perm l m}
     {R:Rel (list A) (list A)}
     {reflR:{l:list A}R l l}
     {symR:{l,m:list A}
           {sym_prem:Perm l m}{sym_ih:R l m} 
            R m l}
     {transR:{l,m,n:list A}
             {lt_prem:Perm l m}{lt_ih:R l m}
             {rt_prem:Perm m n}{rt_ih:R m n} 
              R l n}
     {swapR:{l,m:list A}R (append l m) (append m l)}
     {consclR:{a:A}{m,n:list A}{cons_prem:Perm m n}{cons_ih:R m n}
               R (cons a m) (cons a n)}
     R l m;

Intros;
Refine perm_hyp (andRel Perm R);
andI;
andI;Intros _;andI;Refine reflPerm;Refine reflR;
andI;Intros ___;andE H;andI;Refine symPerm;Refine +1 symR;Try Immed;
     Intros _____;andE H;andE H1;andI;Refine transPerm;Refine +3 transR;Try Immed;

Refine andRelI;
Refine closureInc;

Intros l m base_hyp;
Refine base_hyp (andRel Perm R);
andI;
Intros __;andI;Refine swapPerm;Refine swapR;
Intros a l m cons_hyp;andE cons_hyp;andI;Refine consclPerm;Refine +1 consclR;Try Immed;

intros;Try Immed;
intros;Try Immed;

Save recPerm;

Goal PermE : {R:Rel (list A) (list A)}
     {reflR:{l,m|list A}{eq_prem:Eq l m} R l m}
     {symR:{l,m|list A}
           {sym_prem:Perm l m}{sym_ih:R l m}
            R m l}
     {transR:{l,m,n|list A}
             {lt_prem:Perm l m}{lt_ih:R l m}
             {rt_prem:Perm m n}{rt_ih:R m n}
              R l n}
     {swapR:{l,m|list A}R (append l m) (append m l)}
     {consclR:{a|A}{m,n|list A}{cons_prem:Perm m n}{cons_ih:R m n}
               R (cons a m) (cons a n)}
     SubRel Perm R;

Intros;Refine recPerm;intros +1;Refine reflR;Refine Eq_refl;Try Immed;
Save PermE;

[indPerm = [l,m:list A]{phi:Prop}
((Eq l m)  ->  phi) ->
((Perm m l) -> phi) ->
({k:list A}(Perm l k) -> (Perm k m) -> phi) ->
({h,k:list A}(Eq (append h k) l) -> (Eq (append k h) m) -> phi) ->
({a:A}{h,k:list A}(Eq (cons a h) l) -> (Eq (cons a k) m) -> (Perm h k) -> phi) ->
               phi : Rel (list A) (list A)];

Goal PermIsInductive : SubRel Perm indPerm;
Refine PermE;
Intros;Refine H;Refine eq_prem;
Intros;Refine H1;Refine sym_prem;
Intros;Refine H2;Refine +1 lt_prem;Refine rt_prem;
Intros;Refine H3;Refine +2 Eq_refl;Refine Eq_refl;
Intros;Refine H4;Refine +3 Eq_refl;Refine +1 Eq_refl;Refine cons_prem;
Save PermIsInductive;

[B|Type];

Goal PermRrespR : {R:Rel B (list A)}
     {swapR:{l,m:list A}{h:B}(R h (append l m)) -> R h (append m l)}
     {consclR:{b:A}{l,m:list A}
              {cons_prem:Perm l m}
              {cons_ih:{h:B}(R h l) -> R h m}
     {k:B}(R k (cons b l)) -> R k (cons b m)}
SubRel Perm (impliesRel R R);

intros;

Refine transSubRel;

[kerR = andRel (impliesRel R R) (coimpliesRel (op R) (op R))];

Refine +1 PermE kerR;

intros;andI;
Intros; Qrepl Eq_sym eq_prem; Try Immed;
Intros;Qrepl eq_prem;Try Immed;

intros;andE sym_ih;andI;
Intros;Refine H1;Try Immed;
Intros;Refine H;Try Immed;

intros;andE lt_ih;andE rt_ih;andI;
Intros;Refine H2;Refine H;Try Immed;
Intros;Refine H1;Refine H3;Try Immed;

intros;andI;Refine swapR;Refine swapR;

intros;andE cons_ih;andI;
Intros;Refine consclR;Try Immed;
Intros;Refine consclR;Try Immed;Refine symPerm;Try Immed;

Refine andRelE1;Refine +1 reflSubRel;

Save PermRrespR;

Goal PermLrespR : {R:Rel (list A) B}
     {swapR:{l,m:list A}{h:B}(R (append l m) h) -> R (append m l) h}
     {consclR:{b:A}{l,m:list A}
              {cons_prem:Perm l m}
              {cons_ih:{h:B}(R l h) -> R m h}
     {k:B}(R (cons b l) k) -> R (cons b m) k}
SubRel Perm (coimpliesRel R R);

intros;

Refine transSubRel;

[kerR = andRel (coimpliesRel R R) (impliesRel (op R) (op R))];

Refine +1 PermE kerR;

intros;andI;
Intros; Qrepl eq_prem;Try Immed;
Intros; Qrepl Eq_sym eq_prem;Try Immed;

intros;andE sym_ih;andI;
Intros;Refine H1;Try Immed;
Intros;Refine H;Try Immed;

intros;andE lt_ih;andE rt_ih;andI;
Intros;Refine H;Refine H2;Try Immed;
Intros;Refine H3;Refine H1;Try Immed;

intros;andI;Refine swapR;Refine swapR;

intros;andE cons_ih;andI;
Intros;Refine consclR;Try Immed;Refine symPerm;Try Immed;
Intros;Refine consclR;Try Immed;

Refine andRelE1;Refine +1 reflSubRel;

Save PermLrespR;

Discharge B;

Goal PermPredE : {P:Pred (list A)}
     {swapP:{l,m:list A}(P (append l m)) -> P (append m l)}
     {consclP:{b:A}{l,m:list A}
              {cons_prem:Perm l m}
              {cons_ih:iff (P l) (P m)}
              (P (cons b l)) -> P (cons b m)}
{l,m:list A}{perm_hyp:Perm l m}(P l) -> P m;

intros;Refine PermE [l,m:list A]iff (P l) (P m);Try Immed;

intros;andI;
intros;Qrepl Eq_sym eq_prem;Try Immed;
intros;Qrepl eq_prem;Try Immed;
intros;andE sym_ih;andI;Try Immed;
intros;andE lt_ih;andE rt_ih;andI;
intros;Refine H3;Refine H1;Try Immed;
intros;Refine H2;Refine H4;Try Immed;
intros;andI;Refine swapP;Refine swapP;

intros;andE cons_ih;andI;
Refine consclP;Try Immed;
Refine consclP;Refine symPerm;andI +1;Try Immed;

intros;Refine H1;Try Immed;

Save PermPredE;

Goal nilPermlemma : {l,m|list A}{perm_hyp:Perm l m}(Eq (nil A) l)-> Eq (nil A) m;

intros;Refine PermPredE (Eq (nil A));Try Immed;
intros; Refine append_strict; Refine -1 Eq_sym H1;
intros eql1nil eqm1nil; Qrepl eqm1nil; Refine Eq_sym eql1nil; 

intros; Refine nil_not_cons; Try Immed;
Save nilPermlemma;

Goal nilPerm : {l:list A}{perm_nil:Perm (nil A) l}Eq (nil A) l;
intros;Refine nilPermlemma;Try Immed;Refine Eq_refl;
Save nilPerm;

Goal singletonPermlemma : {l,m:list A}{perm_hyp:Perm l m}
            {a:A}(Eq (singleton a) l) -> Ex [b:A]and (Eq a b) (Eq (singleton b) m);
intros;

Claim Eq (singleton a) m;
exI ?;andI +1;Refine +2 ?+3;Refine Eq_refl;

Refine PermRrespR [a:A][l:list A]Eq (singleton a) l;Try Immed;

intros;Refine insertapp;
Refine -2 Eq_trans; Refine -2 H1; Refine +1 nil; Refine +2 Eq_refl;

(*
Refine +6 H1;Refine +3 Eq_refl;
Refine +1 nil A;Refine +1 nil A;Refine +1 Eq_refl;
*)

intros;Refine H2;
intros;

Refine append_strict; Try Immed;
intros neqnil m1eqnil;
Qrepl m1eqnil; Qrepl Eq_sym H3; Qrepl neqnil;
Refine Eq_refl;

intros;Refine H2;
intros;

Refine append_strict; Try Immed;
intros l1eqnil neqnil;
Qrepl l1eqnil; Qrepl Eq_sym H4; Qrepl neqnil;
Refine Eq_refl;

intros;
Refine cons_inj H1;
intros keqb nileql1; 
Qrepl keqb;
Refine Eq_resp (cons ?);
Refine nilPerm;
Refine transPerm;
Try Immed;
Refine reflPerm';
Refine nileql1;

Save singletonPermlemma;

Goal singletonPerm : {a,b:A}(Perm (singleton a) (singleton b)) -> Eq a b;
intros;Refine singletonPermlemma;Refine +2 H;Refine +1 Eq_refl;
intros;andE H1;Refine Eq_trans;Try Immed;
Refine cons_inj H3; intros; Try Immed;
Save singletonPerm;

Goal PermRespLength : {l,m|list A}{Perm_hyp:Perm l m}Eq (length l) (length m);
Refine PermE [l,m:list A]Eq (length l) (length m);
intros; Refine Eq_resp; Try Immed;
intros;Refine Eq_sym;Refine sym_ih;
intros;Refine Eq_trans;Refine +1 lt_ih;Refine rt_ih;
intros;
Refine Eq_trans; Refine -1 length_append;
Refine Eq_trans; Refine -1 plus_commutes;
Refine Eq_sym; Refine length_append;
intros;Refine Eq_resp suc;Refine cons_ih;
Save PermRespLength;

[a:A];

[PermResidue = [l,m:list A]{phi:Prop}
{ex_hk:{h,k:list A}{perm_lhk:Perm l (append h k)}{ins_hkm:Eq (insert a h k) m}phi}
         phi : Rel (list A) (list A)];

Goal insResidue : {h,k,l:list A}{ins_hkl:Eq (insert a h k) l}PermResidue (append h k) l;

Intros;Refine ex_hk;Try Immed;Refine reflPerm;
Save insResidue;

Goal swapResidue : {l,m,n:list A}{res_nlm:PermResidue n (append l m)}PermResidue n (append m l);

intros;Refine res_nlm;
intros;Refine insertapp;Try Immed;

intros;Refine H;
Intros;Refine ex_hk;
Next -0; Qrepl Eq_sym H1;
Refine Eq_sym; Refine append_assoc;
Refine transPerm;Refine +1 perm_lhk;               (* elininate n            *)
Qrepl Eq_sym H2;
Qrepl append_assoc h n1 m;
Refine symPerm;
Qrepl Eq_sym (append_assoc m h n1);
Refine swapPerm;                                   (* finish with a swap!    *)

intros;Refine H;
Intros;Refine ex_hk;
Next -0; Qrepl Eq_sym H2;
Refine Eq_trans;
Refine +2 append_assoc;
Refine Eq_refl;
Refine transPerm;Refine +1 perm_lhk;               (* eliminate n            *)
Qrepl Eq_sym H1;
Qrepl Eq_sym (append_assoc l n1 k);
Refine symPerm;
Qrepl append_assoc n1 k l;
Refine swapPerm;                                   (* finish with a swap!    *)

Save swapResidue;

Goal consclResidue : {b:A}{l,m:list A}
     {cons_prem:Perm l m}
     {cons_ih:{h:list A}{res_hl:PermResidue h l}PermResidue h m}
     {k:list A}{res_kbl:PermResidue k (cons b l)}PermResidue k (cons b m);

intros;Refine res_kbl;
intros;Refine insertapp (cons b (nil A)) l;Try Immed;

intros;Refine H;
intros;Refine insertsingleton;Try Immed;

Intros nileqh aeqb nileqn __;Refine ex_hk;
Next -0; Qrepl Eq_sym aeqb;
Refine +1 nil A;Refine Eq_refl;                       (* eliminate the equation    *)
Refine transPerm;Refine +1 perm_lhk;                 (* eliminate k               *)
Qrepl Eq_sym H2;
Qrepl Eq_sym nileqh;
Qrepl Eq_sym nileqn;
Refine cons_prem;                                    (* use the premise !         *)

intros;Refine H;
intros;Refine cons_ih (append n k1);Refine insResidue;Try Immed;

Intros;Refine ex_hk;
Next -0; Qrepl Eq_sym ins_hkm1;
Refine Eq_refl (insert a (cons b h1) k2);          (* eliminate the equation    *)
Refine transPerm;Refine +1 perm_lhk;                 (* eliminate k               *)
Qrepl Eq_sym H1;
Refine consclPerm;                                   (* remove the b prefix       *)
Refine perm_lhk1;                                    (* we knew this already!     *)

Save consclResidue;

Goal funopResidue : {h,k,l:list A}{res_hl:PermResidue h l}{res_kl:PermResidue k l}Perm h k;

intros;Refine res_hl;
intros;Refine res_kl;
intros;Refine inseqins;Refine -2 Eq_trans;Refine -2 Eq_sym;
Refine -3 ins_hkm;Refine +2 ins_hkm1;

intros;Refine H;intros;

Refine transPerm;Refine +1 perm_lhk;                 (* eliminate h               *)
Qrepl Eq_sym H2;
Refine symPerm;
Refine transPerm;Refine +1 perm_lhk1;                (* eliminate k               *)
Qrepl Eq_sym H1;

Refine transPerm;Refine +1 transPerm;                       (* get some space     *)
Refine +2 symPerm;
Next +2; Expand insert;
Qrepl Eq_sym (append_assoc h1 (cons a n) k2);
Refine swapPerm;
Next -0; Expand insert;
Qrepl append_assoc h1 n (cons a k2);
Refine swapPerm;
Refine consclPerm;                                          (* remove the a prefix*)
Refine transPerm;Refine +2 swapPerm;
Qrepl Eq_sym (append_assoc h1 n k2);
Refine swapPerm;                         (* rebracket and swap *)


intros;Refine H;
intros;Refine H1;intros h2eqh1 k1eqk2;

Refine transPerm;Refine +1 perm_lhk;                 (* eliminate h               *)
Qrepl Eq_sym h2eqh1;
Refine symPerm;
Refine transPerm;Refine +1 perm_lhk1;                (* eliminate k               *)
Qrepl Eq_sym k1eqk2;
Refine reflPerm;


intros;Refine H1;intros;
Refine transPerm;Refine +1 perm_lhk;                 (* eliminate h               *)
Qrepl Eq_sym H2;
Refine symPerm;
Refine transPerm;Refine +1 perm_lhk1;                (* eliminate k               *)
Qrepl Eq_sym H3;
Refine transPerm;Refine +1 transPerm;                       (* get some space     *)
Refine +2 symPerm;
Next +2; Expand insert;
Qrepl append_assoc h2 n (cons a k1);Refine swapPerm;
Next -0; Expand insert;
Qrepl Eq_sym (append_assoc h2 (cons a n) k1); Refine swapPerm;
Refine consclPerm;
Refine transPerm; 
Next -0; Qrepl Eq_sym (append_assoc n k1 h2); Refine swapPerm;
Qrepl Eq_sym (append_assoc k1 h2 n); Refine reflPerm;

Save funopResidue;

Goal transResiduelemma : {l,m,h|list A}{perm_hyp:Perm l m}{eq_ahl:Eq (cons a h) l}PermResidue h m;

intros;Refine PermRrespR;Try Immed;
intros;Refine swapResidue;Try Immed;
intros;Refine consclResidue;Try Immed;
Refine insResidue (nil A);Try Immed;

Save transResiduelemma;

Goal heredPermlemma : {l,m|list A}(Perm (cons a l) (cons a m)) -> Perm l m;

intros;

[forallPerm : Rel (list A) (list A)
            = [l,m:list A]
              {h,k:list A}{eq1:Eq (cons a h) l}{eq2:Eq (cons a k) m}Perm h k];

Refine PermE forallPerm;Try Immed;

intros;Expand forallPerm;intros;
Refine reflPerm';
Refine (cons_inj ?).snd;
Refine -0 Eq_trans; Try Immed;
Next -0; Qrepl eq_prem;
Refine Eq_sym; Try Immed;

intros;Expand forallPerm;intros;
Refine symPerm;Refine sym_ih;Try Immed;

intros;Expand forallPerm;intros;
Refine funopResidue;
Refine +1 transResiduelemma lt_prem eq1;
Refine transResiduelemma (symPerm rt_prem) eq2;

Refine list_elim [l:list A]{m:list A}forallPerm (append l m) (append m l);
intros;Expand forallPerm;intros;
Refine reflPerm';
Refine (cons_inj ?).snd;
Refine -0 Eq_trans; Try Immed;
Refine -0 Eq_trans; Refine -1 Eq_sym; Refine -1 append_nil;
Refine -0 Eq_sym; Try Immed;

intros;
Refine list_elim [m:list A]forallPerm (append ? m) (append m ?);

Intros h n eq1 eq2;
Refine cons_inj eq1; intros;
Refine cons_inj eq2; intros;
Qrepl H2; Qrepl H4; Equiv Perm (append ??) ?;
Qrepl append_nil x2; 
Refine reflPerm;

Intros c n _ h j eq1 eq2;

(*
[aeqb = headlemma eq1 (Eq_refl ?) : Eq a b];
[aeqc = headlemma eq2 (Eq_refl ?) : Eq a c];
[kcneqh : Eq (insert c k n) h = Eq_sym (taillemma eq1 (Eq_refl ?))];
[nbkeqj : Eq (insert b n k) j = Eq_sym (taillemma eq2 (Eq_refl ?))];
*)

Refine cons_inj eq1; Refine cons_inj eq2; intros; 
Qrepl H4; Qrepl H2; Equiv Perm (append ??) (append ??);
Qrepl Eq_sym H1; Qrepl H3; Refine symPerm;
Refine transPerm;Refine +2 swapPerm;
Refine transPerm;Refine +1 swapPerm;
Refine consclPerm;Refine swapPerm;

Intros b h j cons_prem _ k n eq1 eq2;
Refine cons_inj eq1; Refine cons_inj eq2; intros;
Qrepl H4; Qrepl H2; Try Immed;

Refine Eq_refl;Refine Eq_refl;

Save heredPermlemma;

Discharge a;

[hereditary [S:Rel (list A) (list A)] = {l:list A}SubRel (appcl l S) S];

Goal heredPerm : hereditary Perm;

Refine list_elim [l:list A]SubRel (appcl l Perm) Perm;
Intros ___;Try Immed;
intros;Intros ___;Refine x2_ih;Refine heredPermlemma;Try Immed;
Save heredPerm;

Goal transposePerm : {a,b|A}{l,m,n|list A}Perm (insert a l (insert b m n)) (insert b l (insert a m n));
intros;
Refine appclPerm;
Refine transPerm;
Refine +2 swapPerm (cons a n) (cons b m);
Refine consclPerm;
Refine transPerm;
Refine +1 swapPerm;
Refine transPerm;
Refine +2 swapPerm;
Refine consclPerm;
Refine swapPerm;
Save transposePerm;

Discharge A;
