Module lib_int_nat_lemmas Import lib_nat_Prop_rels;


Goal weird_thing : {x,y,a,b:nat}(Eq (plus (times x a) (times y b))
 (plus (times x b) (times y a))) -> (or (Eq x y) (Eq a b));
intros x y a b;
Refine nat_diagonal_ind [x,y:nat](Eq (plus (times x a) (times y b))
 (plus (times x b) (times y a))) -> (or (Eq x y) (Eq a b));
intros m;
Refine nat_ind [m:nat](Eq (plus (times zero a) (times m b)) 
    (plus (times zero b) (times m a)))->or (Eq zero m) (Eq a b);
intros;
Refine inl; Refine Eq_refl;
intros;
Refine inr;
Refine times_cancel_right;
Refine n;
Refine Eq_sym;
Qrepl times_commutes|b|(suc n);
Qrepl times_commutes|a|(suc n);
Refine H1;
intros;
Refine inr;
Refine times_cancel_right;
Refine n;
Qrepl times_commutes|b|(suc n);
Qrepl times_commutes|a|(suc n);
Qrepl Eq_sym (plus_zero (times (suc n) a));
Qrepl Eq_sym (plus_zero (times (suc n) b));
Refine H;
intros;
Refine H;
Refine cancel_plus;
Refine plus a b;
Refine Eq_trans;
Refine +1 middle_four_plus;
Qrepl plus_commutes a b;
Refine Eq_trans;
Refine +2 middle_four_plus;
Refine H1;
intros; Refine inl;
Refine Eq_resp suc;
Refine H2;
intros; Refine inr; Refine H2;
Save weird_thing;

Goal weird_Lt : {x,y,a,b:nat}(Lt x y) -> (Lt a b) ->
    (Lt (plus (times x b) (times y a)) (plus (times x a) (times y b)));
Intros x y a b;
Refine nat_diagonal_ind [x,y:nat]((Lt x y)->(Lt a b)->Lt (plus (times x b) (times y a)) (plus (times x a) (times y b)));
intros;
Refine (ze_Lt_imp_Eq_suc ? H); intros;
Qrepl H2;
Refine Lt_resp_times;
Refine H1;
intros;
Refine not_n_Lt_zero;
Refine +1 H;
intros;
Qrepl middle_four_plus|b|a|(times n b)|(times m a);
Qrepl middle_four_plus|a|b|(times n a)|(times m b);
Qrepl plus_commutes b a;
Refine Lt_resp_plus;
Refine H;
Refine Lt_resp_pred;
Refine H1; Refine H2;
Save weird_Lt;

Goal weird_Le : {x,y,a,b:nat}(Le x y) -> (Le a b) ->
    (Le (plus (times x b) (times y a)) (plus (times x a) (times y b)));
Intros x y a b;
Refine nat_diagonal_ind [x,y:nat]((Le x y)->(Le a b)->Le (plus (times x b) (times y a)) (plus (times x a) (times y b)));
intros;
Refine Le_resp_times;
Refine H1;
intros;
Refine not_Le_zero_n;
Refine +1 H;
intros;
Qrepl middle_four_plus|b|a|(times n b)|(times m a);
Qrepl middle_four_plus|a|b|(times n a)|(times m b);
Qrepl plus_commutes b a;
Refine Le_resp_plus;
Refine H;
Refine Le_resp_pred;
Refine H1; Refine H2;
Save weird_Le;

Goal weird_thing_Le : {x,y,a,b:nat}(Le (plus (times x a) (times y b))
 (plus (times x b) (times y a))) -> 
(Lt x y) -> (Le b a);
intros x y a b;
Refine nat_diagonal_ind [x,y:nat]((Le (plus (times x a) (times y b)) (plus (times x b) (times y a)))->(Lt x y)->Le b a);
intros;
Refine (ze_Lt_imp_Eq_suc ? H1);intros;
Refine Le_times_cancel;
Refine t;
Qrepl Eq_sym H2;
Qrepl times_commutes|b|m;
Qrepl times_commutes|a|m;
Refine H;
intros;
Refine not_n_Lt_zero;
Refine +1 H1;
intros;
Refine H;
Refine Le_resp_sub;
Refine plus a b;
Qrepl middle_four_plus|a|(times n a)|b|(times m b);
Qrepl plus_commutes a b;
Qrepl middle_four_plus|b|(times n b)|a|(times m a);
Refine H1;
Refine Lt_resp_pred;
Refine H2;
Save weird_thing_Le;

Goal weird_thing_Lt : {x,y,a,b:nat}(Lt (plus (times x a) (times y b))
 (plus (times x b) (times y a))) -> 
(Lt x y) -> (Lt b a);
intros x y a b;
Refine nat_diagonal_ind [x,y:nat]((Lt (plus (times x a) (times y b)) (plus (times x b) (times y a)))->(Lt x y)->Lt b a);
intros;
Refine (ze_Lt_imp_Eq_suc ? H1);intros;
Refine Lt_times_cancel; (* Doesn't exist *)
Refine t;
Qrepl Eq_sym H2;
Qrepl times_commutes|b|m;
Qrepl times_commutes|a|m;
Refine H;
intros;
Refine not_n_Lt_zero;
Refine +1 H1;
intros;
Refine H;
Refine Lt_resp_sub;
Refine plus a b;
Qrepl middle_four_plus|a|(times n a)|b|(times m b);
Qrepl plus_commutes a b;
Qrepl middle_four_plus|b|(times n b)|a|(times m a);
Refine H1;
Refine Lt_resp_pred;
Refine H2;
Save weird_thing_Lt;
