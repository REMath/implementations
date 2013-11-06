Module lib_nat_bool_rels Import lib_nat_suc_thms
                                lib_bool_thms;

(* Contents
   --------
   o Definitions of bool-valued less-than, less-or-equal, equal and odd
     relations on the natural numbers
   o Several theorems about these relations


   Changes
   -------

   Thomas Schreiber <16 Jan 1996>
   added definition of `odd'

                    <2 Feb 1996>
   added theorem nat_eq_character'

*)

[    lt = nat_iter 
                 (nat_iter false ([_:bool]true))
                 ([ltn:nat->bool]nat_rec false ([x:nat][_:bool]ltn x))
            : nat->nat->bool 
]
[    le = nat_iter 
                 ([m:nat]true)
                 ([len:nat->bool]nat_rec false ([x:nat][_:bool]len x))
            : nat->nat->bool
]
[    nat_eq = nat_iter 
                 (nat_iter true ([_:bool]false))
	         ([eqn:nat->bool]nat_rec false ([x:nat][_:bool]eqn x))
            : nat->nat->bool 
];

Goal zero_lt_suc : {n:nat} is_true (lt zero (suc n));
 intros _;Refine Eq_refl;
Save zero_lt_suc;                                                      


Goal zero_le_suc : {n:nat} is_true (le zero (suc n));
 intros _;Refine Eq_refl;
Save zero_le_suc;                                                      


Goal not_n_lt_zero : {n:nat} is_false (lt n zero);
 Refine nat_ind [n:nat] is_false (lt n zero);
 Refine Eq_refl;
 intros; Refine Eq_refl;
Save not_n_lt_zero;                                                    


Goal lt_resp_suc : {n,m:nat} Eq (lt n m) (lt (suc n) (suc m));
 Refine nat_double_elim[n,m:nat]Eq (lt n m) (lt (suc n) (suc m));
 Refine Eq_refl;
 intros; Refine Eq_refl;
 intros; Refine Eq_refl;
 intros; Refine Eq_refl;
Save lt_resp_suc;                                                      


Goal le_resp_suc : {n,m:nat} Eq (le n m) (le (suc n) (suc m));
 Refine nat_double_elim[n,m:nat]Eq (le n m) (le (suc n) (suc m));
 Refine Eq_refl;
 intros; Refine Eq_refl;
 intros; Refine Eq_refl;
 intros; Refine Eq_refl;
Save le_resp_suc;                                                      


Goal not_n_lt_n : {n:nat} is_false (lt n n);
 Refine nat_ind [n:nat]is_false (lt n n);
 Refine Eq_refl;
 intros; Try Immed;
Save not_n_lt_n;                                                        


Goal n_lt_suc_n : {n:nat} is_true (lt n (suc n));
 Refine nat_ind [n:nat] is_true (lt n (suc n));
 Refine Eq_refl;
 intros; Try Immed;
Save n_lt_suc_n;                                                        


Goal not_lt_suc_is_suc : {m,n:nat} (is_false (lt m (suc n))) -> is_suc m;
 Refine nat_ind [m:nat] {n:nat} (is_false (lt m (suc n))) -> is_suc m;
 intros n H; Refine true_not_false; Refine H;
 intros n H n1 H1; exI ?; Refine n; Refine Eq_refl;
Save not_lt_suc_is_suc;                                                  


Goal lt_weak_trans : {m,n|nat}(is_true (lt m n))->(is_true (lt m (suc n)));
 Refine nat_double_elim [m,n:nat] (is_true (lt m n))->is_true (lt m (suc n));
 intros; Refine Eq_refl;
 intros; Refine Eq_refl;
 intros; Refine true_not_false;
 Refine Eq_subst (not_n_lt_zero (suc m)); Try Immed; Refine Eq_sym H1;
 intros; Refine H n H2;
Save lt_weak_trans;


Goal lt_left_suc : {n,m:nat}(is_true (lt (suc n) m))->(is_true (lt n m));
 Refine nat_double_elim [n,m:nat](is_true (lt (suc n) m))->(is_true (lt n m));
 intros; Refine true_not_false; 
 Refine Eq_subst (not_n_lt_zero one); Refine Eq_sym H;
 intros; Refine Eq_refl;
 intros; Refine Eq_subst (not_n_lt_zero (suc (suc m))); Try Immed;
 intros; Refine H n H2;
Save lt_left_suc;


Goal lt_suc_character : {m,n:nat}(is_true (lt n (suc m)))->(or (Eq n m) (is_true (lt n m)));
 Refine nat_double_elim [m,n:nat] (is_true (lt n (suc m)))->
                                      (or (Eq n m) (is_true (lt n m)));
 intros; orIL; Refine Eq_refl;
 intros; Refine true_not_false; 
 Refine Eq_subst (not_n_lt_zero n); Refine Eq_sym H1;
 intros; orIR; Refine Eq_refl;
 intros; orE H n H2;
 intros; orIL; Refine Eq_resp; Try Immed;
 intros; orIR; Try Immed;
Save lt_suc_character;


Goal lt_character : {n,m:nat}or (and (is_true (lt n m)) (is_false (lt m n)))
             (or (and (is_true (lt m n)) (is_false (lt n m)))
                  (Eq n m));
 Refine nat_double_elim [n,m:nat]
              or (and (is_true (lt n m)) (is_false (lt m n)))
             (or (and (is_true (lt m n)) (is_false (lt n m)))
                  (Eq n m));
 orIR; orIR; Refine Eq_refl;
 intros; orIL; andI; Refine Eq_refl; Refine Eq_refl;
 intros; orIR; orIL; andI; Refine Eq_refl; Refine Eq_refl;
 intros; orE H n;
 intros; orIL; andI; Refine fst H2; Refine snd H2;
 intros; orE H2;
 intros; orIR; orIL; andI; Refine fst H3; Refine snd H3;
 intros; orIR; orIR; Refine Eq_resp; Try Immed;
Save lt_character;


Goal le_character : {n,m:nat}or (and (is_true (le n m)) (is_false (le m n)))
             (or (and (is_true (le m n)) (is_false (le n m)))
                 (Eq n m));
 Refine nat_double_elim [n,m:nat]
               or (and (is_true (le n m)) (is_false (le m n)))
              (or (and (is_true (le m n)) (is_false (le n m)))
                  (Eq n m));
 orIR; orIR; Refine Eq_refl;
 intros; orIL; andI; Refine Eq_refl; Refine Eq_refl;
 intros; orIR; orIL; andI; Refine Eq_refl; Refine Eq_refl;
 intros; orE H n;
 intros; orIL; andI; Refine fst H2; Refine snd H2;
 intros; orE H2;
 intros; orIR; orIL; andI; Refine fst H3; Refine snd H3;
 intros; orIR; orIR; Refine Eq_resp; Try Immed;
Save le_character;

Goal le_refl : {n:nat} is_true (le n n);
Refine nat_ind [n:nat] is_true (le n n);
Refine Eq_refl;
intros;
Try Immed;
Save;

Goal le_zero_imp_zero : {n:nat} iff (is_true (n .le zero)) (n .Eq zero);
intros;
andI;
Refine nat_ind [n:nat](is_true (le n zero))->Eq n zero;
intros; Refine Eq_refl;
intros;
Refine true_not_false;
Refine Eq_sym; Try Immed;
intros;
Qrepl H;
Refine Eq_refl;
Save le_zero_imp_zero;



Goal le_not_lt_imp_Eq : {i,n:nat}((is_true (i .le n)) /\ (is_false (i .lt n))) -> (Eq i  n);
intros i n;
Refine nat_ind [n:nat]{i:nat}(and (is_true (le i n)) (is_false (lt i n)))->Eq i n;
intros;
Refine fst (le_zero_imp_zero ?);
Refine fst H;
intros _ ind_hypoth _;
Refine zero_or_suc i1;
intros i1_Eq_zero;
Qrepl i1_Eq_zero;
intros le_and_not_lt;
Refine bool_contradiction;
Refine +2 snd le_and_not_lt;
Refine Eq_refl;
intros i1_is_suc;
Refine i1_is_suc;
intros _ suc_t_eq_i1;
Qrepl Eq_sym suc_t_eq_i1;
intros;
Refine Eq_resp;
Refine ind_hypoth;
andI;
Refine Eq_trans;
Refine +1 le_resp_suc;
Refine fst; Try Immed;
Refine Eq_trans;
Refine +1 lt_resp_suc;
Refine snd; Try Immed;
Save le_not_lt_imp_Eq;

Goal lt_imp_le_suc : {x,y|nat} (is_true (x .lt y)) -> is_true ((suc x) .le y);
intros _ _;
Refine nat_ind [y:nat]{x:nat}(is_true (lt x y))->is_true (le (suc x) y);
intros;
Refine true_not_false;
Qrepl Eq_sym H;
Refine not_n_lt_zero;
intros n ind_hyp _;
Qrepl Eq_sym (le_resp_suc x1 n);
Refine zero_or_suc x1;
intros x1_is_zero _;
Qrepl x1_is_zero;
Refine Eq_refl;
intros x1_is_suc;
Refine x1_is_suc;
intros _ suc_t_is_x1;
Qrepl Eq_sym suc_t_is_x1;
intros;
Refine ind_hyp;
Qrepl lt_resp_suc t n;
Try Immed;
Save lt_imp_le_suc;

Goal nat_eq_character : {m,n:nat}iff (is_true (nat_eq m n)) (Eq m n);
 Refine nat_double_elim [m,n:nat]iff (is_true (nat_eq m n)) (Eq m n);
 andI; intros; Refine Eq_refl; intros; Refine Eq_refl;
 intros; andI; intros; Refine true_not_false (Eq_sym H1);
 intros; Refine zero_not_suc n H1;
 intros; andI; intros; Refine true_not_false (Eq_sym H1);
 intros; Refine zero_not_suc m (Eq_sym H1);
 intros; andE H n; andI;
 intros; Refine Eq_resp; Refine H2 H4;
 intros; Refine H3; Refine suc_injective H4;
Save nat_eq_character;

Goal nat_eq_character' : {m,n:nat}iff (is_false (nat_eq m n)) (not (Eq m n));
intros; 
Refine pair;
  Intros __;
    Refine bool_contradiction; Try Immed;
    Refine snd (nat_eq_character ??); Try Immed;
  intros;
    Refine fst (inv_is_true_is_false ?);
    Refine snd (inv_character ?);
    Intros _; Refine H;
      Refine fst (nat_eq_character ??); Try Immed;
Save;

Goal nat_eq_sym : {m,n:nat}Eq (nat_eq m n) (nat_eq n m);
 Refine nat_double_elim [m,n:nat] Eq (nat_eq m n) (nat_eq n m);
 Refine Eq_refl;
 intros; Refine Eq_refl;
 intros; Refine Eq_refl;
 intros; Qrepl H n; Refine Eq_refl;
Save nat_eq_sym;


Goal nat_eq_refl : {n:nat} is_true (nat_eq n n);
 Refine nat_ind [n:nat] is_true (nat_eq n n);
 Refine Eq_refl; intros; Try Immed;
Save nat_eq_refl;


Goal odd: {n:nat}bool;
Refine nat_iter;
Refine false;			(* odd 0 *)
Refine inv;
Save;

Goal even: {n:nat}bool;
Refine nat_iter;
Refine true;			(* even 0 *)
Refine inv;
SaveUnfrozen;
