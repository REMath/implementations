Module lib_nat_plus_thms Import lib_nat_suc_thms;

(* Contents
   --------
   o Basic theorems about addition of naturals
*)

Goal plus_zero : {n:nat}Eq (plus n zero) n;
    Refine nat_ind [n:nat]Eq (plus n zero) n;
    Refine Eq_refl;
    intros n ih; Refine Eq_resp_suc ih;
Save plus_zero;                                                          


Goal plus_suc : {m,n:nat}Eq (plus m (suc n)) (suc (plus m n));
    intros m n;
    Refine nat_ind ([m:nat]Eq (plus m (suc n)) (suc (plus m n)));
    Refine Eq_refl;
    intros x ih; Refine Eq_resp_suc ih;
Save plus_suc;                                                           


Goal plus_suc_lemma : {x,t:nat}(not (Eq (plus x (suc t)) x));
    intros;
    Refine nat_ind [x:nat](not (Eq (plus x (suc t)) x));
    Intros H;
    Refine zero_not_suc;
    Refine +1 Eq_sym H;
    intros;
    Intros H1; Refine H;
    Refine suc_injective;
    Refine H1;
Save plus_suc_lemma;


Goal plus_assoc : {k,m,n:nat}Eq (plus (plus k m) n) (plus k (plus m n));
    Intros k m n;
    Refine nat_ind [k:nat] Eq (plus (plus k m) n) (plus k (plus m n));
    Refine Eq_refl;
    intros x ih;  Refine Eq_resp suc ih;
Save plus_assoc;                                                        


Goal plus_commutes : {m,n:nat}Eq (plus m n) (plus n m);
    intros m n;
    Refine nat_ind [m:nat]Eq (plus m n) (plus n m);
    Refine Eq_sym (plus_zero n);
    intros x ih;
    Refine Eq_trans; Refine suc (plus n x); Refine Eq_resp_suc ih;
    Qrepl plus_suc n x; Refine Eq_refl;
Save plus_commutes;                                                       


Goal plus_strict : {n,m|nat}(Eq (plus n m) zero)->and (Eq n zero) (Eq m zero);
    intros n;
    Refine nat_ind [m|nat](Eq (plus n m) zero)->and (Eq n zero) (Eq m zero);
    intros; Refine pair; 
    Refine Eq_trans (Eq_sym (plus_zero n)) H; Refine Eq_refl;
    intros; Refine zero_not_suc (plus n n1); Qrepl (Eq_sym (plus_suc n n1)); 
    Refine Eq_sym H1;
Save plus_strict;     


Goal middle_four_plus : {i,j,k,l|nat}Eq (plus (plus i k) (plus j l)) (plus (plus i j) (plus k l));
    intros;
    Refine nat_ind [k:nat]
       {i,j,l|nat}Eq (plus (plus i k) (plus j l)) (plus (plus i j) (plus k l));
    Try Immed;
    intros;Qrepl (plus_zero i1);Refine Eq_sym (plus_assoc ? ? ?);
    intros;
    Qrepl (plus_suc i1 n);
    Qrepl (plus_suc (plus i1 j1) (plus n l1));
    Refine Eq_resp suc;
    Try Immed;
Save middle_four_plus;


Goal one_plus_lemma : {m,n|nat}{eq0:Eq one (plus m n)}
    or (and (Eq one m) (Eq zero n)) (and (Eq zero m) (Eq one n));
    intros;Refine nat_ind [m:nat]{n|nat}{eq0:Eq one (plus m n)}
        or (and (Eq one m) (Eq zero n)) (and (Eq zero m) (Eq one n));Try Immed;
    intros;Refine inr;Refine pair;Refine Eq_refl;Try Immed;
    intros; Refine plus_strict;
    Refine +2 Eq_sym (suc_injective eq01);
    intros eq1 eq2;Refine inl;Refine pair;
    Refine Eq_resp;
    Refine Eq_sym eq1;
    Refine Eq_sym eq2;
Save one_plus_lemma;

 
Goal cancel_plus : {i,j,k:nat}(Eq (plus i j) (plus i k))->Eq j k;
    Refine nat_ind [i:nat]{j,k:nat}(Eq (plus i j) (plus i k))->Eq j k;
    intros;Try Immed;
    intros;Refine H;Refine suc_injective;Try Immed;
Save cancel_plus;

                                                  
[    plus_subst_l = [l,n,m|nat][p:Eq l n]Eq_resp ([o:nat](plus o m):nat->nat) p
            : {l,n,m|nat}(Eq l n)->Eq (plus l m) (plus n m) 
]
[    plus_subst_r = [l,n,m|nat][p:Eq l n]
                             Eq_resp ([o:nat](plus m o)) p   
            : {l,n,m|nat}(Eq l n)->Eq (plus m l) (plus m n) 
];






