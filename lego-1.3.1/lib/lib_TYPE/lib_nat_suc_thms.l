Module lib_nat_suc_thms Import lib_nat;

(* Time-stamp: <21 Jul 95 tms ~/library/new/lib_nat/lib_nat_suc_thms.l> *)

(* Contents
   --------
   o Simple theorems about successor and predecessor.
*) 
 
[    Eq_resp_suc = [m,n|nat][p:Eq m n]Eq_resp suc p
           : {m,n|nat}(Eq m n)-> Eq (suc m) (suc n) 
]
[    Eq_resp_pred = [m,n|nat][p:Eq m n]Eq_resp (pred:nat->nat) p
           : {m,n|nat}(Eq m n)-> Eq (pred m) (pred n) 
]
[    suc_injective = [m,n|nat][p:Eq (suc m) (suc n)]Eq_resp_pred p
           : {m,n|nat}(Eq (suc m) (suc n))-> Eq m n
];

Goal n_not_suc_n : {n:nat}not (Eq n (suc n));
    Refine nat_ind [n:nat]not (Eq n (suc n));
    Refine zero_not_suc;
    Intros x ih hyp; Refine ih; Refine suc_injective; Immed;
Save n_not_suc_n;                                                          


Goal suc_pred : {n|nat}(not (Eq n zero)) -> Eq n (suc (pred n));
Refine nat_ind [n:nat](not (Eq n zero)) -> Eq n (suc (pred n));
intros contradiction; Refine contradiction; Refine Eq_refl;
intros; Refine Eq_refl;
Save;






