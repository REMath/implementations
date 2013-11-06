Module lib_nat_minus_thms Import lib_nat_plus_thms;

(* Contents
   --------
   o Various theorems about subtraction.
*)


Goal minus_suc_pred : {n,m:nat}Eq (minus n (suc m)) (minus (pred n) m);
    intros n;
    Refine nat_ind [m:nat]Eq (minus n (suc m)) (minus (pred n) m);
    intros; Refine Eq_refl;
    intros n ih;
    Refine Eq_resp_pred; Try Immed;
Save minus_suc_pred;                                                      


Goal minus_resp_suc : {m,n:nat}Eq (minus (suc m) (suc n)) (minus m n);
    intros; Qrepl minus_suc_pred (suc m) n; Refine Eq_refl;
Save minus_resp_suc;                                                   


Goal n_minus_n_Eq_zero : {n:nat}Eq (minus n n) zero;
    Refine nat_ind [n:nat]Eq (minus n n) zero;
    Refine Eq_refl;
    intros n ih; Qrepl minus_suc_pred (suc n) n; Try Immed;
Save n_minus_n_Eq_zero;                                                     


Goal zero_minus_n_Eq_zero : {n:nat}Eq (minus zero n) zero;
    Refine nat_ind [n:nat]Eq (minus zero n) zero;
    Refine Eq_refl;
    intros n ih; Qrepl minus_suc_pred zero n; Try Immed;
Save zero_minus_n_Eq_zero;                                                  


Goal minus_commutes_suc_l : {m,n,t|nat}
      (Eq (minus n m) (suc t))->Eq (minus (suc n) m) (suc (minus n m));
    Refine nat_double_elim [m,n:nat]{t:nat}(Eq (minus n m) (suc t))->
                                   Eq (minus (suc n) m) (suc (minus n m));
    intros; Refine Eq_refl;
    intros; Refine Eq_refl;
    intros; Refine zero_not_suc t; Qrepl Eq_sym H1;
    Qrepl zero_minus_n_Eq_zero (suc m); Refine Eq_refl;
    intros; Qrepl minus_resp_suc (suc n) m; Qrepl minus_resp_suc n m;
    Refine H ? t; Qrepl Eq_sym (minus_resp_suc n m); Try Immed;
Save minus_commutes_suc_l;                                              

Goal minus_commutes_suc_r : {m,n,t|nat}(Eq (minus n m) (suc t))->Eq (minus n (suc m)) t;
intros;
Equiv Eq (pred (minus n m)) t;
Qrepl H; Refine Eq_refl;
Save minus_commutes_suc_r;

Goal minus_monotone_l : {l:nat}{m,n,t|nat}
        (Eq (minus n m) (suc t))->Eq (minus (plus n l) m) (suc (plus t l));
    Refine nat_ind [l:nat]{m,n,t|nat}(Eq (minus n m) (suc t))->
         Eq (minus (plus n l) m) (suc (plus t l));
    intros; Qrepl plus_zero n; Qrepl plus_zero t; Try Immed;
    intros; Qrepl plus_suc n1 n; Qrepl plus_suc t n; 
    Refine H|m|(suc n1)|(suc t);
    Qrepl Eq_sym H1; Refine minus_commutes_suc_l H1;
Save minus_monotone_l;                                                   
 
Goal minus_inv_plus : {m,n:nat}Eq n (minus (plus m n) m);
intros;
Refine nat_ind [m:nat]Eq n (minus (plus m n) m);
Refine Eq_refl;
intros;
Equiv Eq n (minus (suc (plus (n1) n)) (suc n1));
Qrepl minus_resp_suc (plus n1 n) n1;
Refine H;
Save minus_inv_plus;


Goal nonzero_inv_sp : {x:nat}~(Eq x zero)->(Eq (suc (pred x)) x);
Refine nat_ind[x:nat]~(Eq x zero)->(Eq (suc (pred x)) x);
intros;
Refine H;
Refine Eq_refl;
intros;
Refine Eq_refl;
Save nonzero_inv_sp;




