Module lib_nat_sqrt Import lib_nat_iter lib_nat_rels;

square == [n:nat]times n n;

sqrt == [n:nat]nat_iter zero ([a:nat]if (le (square (suc a)) n) 
                        (suc a) a) n;

Goal sqrt_cor : {n:nat}(Le (square (sqrt n)) n)/\(Lt n (square (suc (sqrt n))));
intros;
Refine pair;
Refine le_true_imp_Le;
Refine while_cond1 [a:nat]le (square a) n;
Refine Le_imp_le_true;
Refine Le_zero_n;
Refine while_cond2 ([a:nat]le (square a) n) n;
intros;
Qrepl H;
Refine Le_imp_Lt_suc';
Refine Le_trans ? (Le_resp_times one (suc n) (suc n) ?);
Refine eq_imp_Le;
Refine Eq_trans (times_one|?) (times_commutes|?|?);
Refine Le_resp_suc;
Refine Le_zero_n;
Refine le_false_imp_Lt;
Save sqrt_cor;

Goal sqrt_small : {n:nat}(Lt one n)->Lt (sqrt n) n;
intros;
Refine decide_nat n (sqrt n);
intros;
Refine not_refl_Lt n;
Refine Lt_Le_trans ? (fst (sqrt_cor ?));
Refine Lt_Le_trans ? (Le_resp_times_both ???? H1 H1);
Refine ze_Lt_imp_Eq_suc ? (Le_imp_Lt_suc' ?? (Lt_imp_Le ?? H));
intros;
Qrepl H2;
Refine Le_Lt_trans ? (Lt_resp_times one ?? ?);
Refine eq_imp_Le;
Refine Eq_trans (times_one|?) (times_commutes|?|?);
Refine Eq_subst H2;
Refine H;
Refine PropId;
Save sqrt_small;
