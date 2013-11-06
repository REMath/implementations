Module lib_nat_rels Import lib_nat_Prop_rels lib_nat_bool_rels;

(* Contents
   --------
   o Theorems concerning the relationship between the Prop-valued relations
     on the naturals (Lt, Le, and Eq) and the bool-valued relations on the
     naturals (lt, le, and nat_eq)
*)

Goal le_true_imp_Le : {n,m:nat}(Eq (le n m) true) -> (Le n m);
intros n m;
Refine nat_diagonal_ind [n,m:nat](Eq (le n m) true)->Le n m;
intros;
Refine Le_zero_n;
intros;
Refine true_not_false;
Refine Eq_sym; Refine H;
intros;
Refine Le_resp_suc;
Refine H;
Refine H1;
Save le_true_imp_Le;


Goal le_false_imp_Lt : {n,m:nat}(Eq (le n m) false) -> (Lt m n);
intros n m;
Refine nat_diagonal_ind [n,m:nat]((Eq (le n m) false)->Lt m n);
intros;
Refine true_not_false;
Refine H;
intros;
Refine zero_Lt_suc_n;
intros;
Refine Lt_resp_suc ? ?;
Refine H;
Refine H1;
Save le_false_imp_Lt;


Goal Le_imp_le_true : {n,m:nat}(Le n m) -> (Eq (le n m) true);
intros n m;
Refine nat_diagonal_ind [n,m:nat](Le n m)->Eq (le n m) true;
intros;
Refine Eq_refl;
intros;
Refine not_Le_zero_n;
Refine +1 H;
intros;
Refine H;
Refine Le_resp_pred;
Refine H1;
Save Le_imp_le_true;


Goal Lt_imp_le_false : {n,m:nat}(Lt m n) -> (Eq (le n m) false);
intros n m;
Refine nat_diagonal_ind [n,m:nat]((Lt m n)->Eq (le n m) false);
intros;
Refine not_n_Lt_zero;
Refine +1 H;
intros;
Refine Eq_refl;
intros;
Refine H;
Refine Lt_resp_pred;
Refine H1;
Save Lt_imp_le_false;


Goal lt_true_imp_Lt : {n,m:nat}(Eq (lt n m) true) -> (Lt n m);
intros n m;
Refine nat_diagonal_ind [n,m:nat]((Eq (lt n m) true)->Lt n m);
Refine nat_ind [m:nat](Eq (lt zero m) true)->Lt zero m;
intros;
Refine true_not_false;
Refine Eq_sym H;
intros;
Refine zero_Lt_suc_n;
intros;
Refine true_not_false;
Refine Eq_sym H;
intros;
Refine Lt_resp_suc ? ?;
Refine H;
Refine H1;
Save lt_true_imp_Lt;

Goal lt_false_imp_Le : {n,m:nat}(Eq (lt n m) false) -> (Le m n);
intros n m;
Refine nat_diagonal_ind [n,m:nat]((Eq (lt n m) false)->Le m n);
Refine nat_ind [m:nat]((Eq (lt zero m) false)->Le m zero);
intros;
Refine eq_imp_Le;
Refine Eq_refl;
intros;
Refine true_not_false;
Refine H1;
intros;
Refine Le_zero_n;
intros;
Refine Le_resp_suc ? ?;
Refine H;
Refine H1;
Save lt_false_imp_Le;


Goal Lt_imp_lt_true : {n,m:nat}(Lt n m)->Eq (lt n m) true;
Refine nat_diagonal_ind [n,m:nat](Lt n m)->Eq (lt n m) true;
Refine nat_ind [m:nat](Lt zero m)->Eq (lt zero m) true;
intros;
Refine not_n_Lt_zero zero H;
intros;
Refine Eq_refl;
intros;
Refine not_n_Lt_zero ? H;
intros;
Qrepl H;
Refine Lt_resp_pred ? ? H1;
Refine Eq_refl;
Save Lt_imp_lt_true;


Goal Le_imp_lt_false : {n,m:nat}(Le n m)->Eq (lt m n) false;
Refine nat_diagonal_ind [n,m:nat](Le n m)->Eq (lt m n) false;
Refine nat_ind [m:nat](Le zero m)->Eq (lt m zero) false;
intros;
Refine Eq_refl;
intros;
Refine Eq_refl;
intros;
Refine not_Le_zero_n ? H;
intros;
Qrepl H;
Refine Le_resp_pred ? ? H1;
Refine Eq_refl;
Save Le_imp_lt_false;

