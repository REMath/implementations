Module lib_nat_Prop_rels Import lib_nat_Lt lib_nat_Le;

(* Contents
   --------
   o Theorems relating to the interaction between the orderings "Lt" and "Le".
*)

Goal Lt_Le_trans : {x,y,z|nat}(Lt x y) -> (Le y z) ->(Lt x z);
intros;
Refine H; intros;
Refine H1; intros;
Refine ExIntro;
Refine plus t t1;
Qrepl Eq_sym H3;
Qrepl Eq_sym H2;
Qrepl plus_suc x (plus t t1);
Qrepl plus_suc|x|t;
Refine Eq_resp;
Refine Eq_sym (plus_assoc ? ? ?);
Save Lt_Le_trans;


Goal Le_Lt_trans : {x,y,z|nat}(Le x y) -> (Lt y z) ->(Lt x z);
intros;
Refine H; intros;
Refine H1; intros;
Refine ExIntro;
Refine plus t t1;
Qrepl Eq_sym H3;
Qrepl Eq_sym H2;
Qrepl plus_suc x (plus t t1);
Qrepl plus_suc (plus x t) t1;
Refine Eq_resp suc;
Refine Eq_sym (plus_assoc ? ? ?);
Save Le_Lt_trans;


Goal Lt_imp_Le : {x,y:nat}(Lt x y) -> (Le x y);
intros;
Refine H; intros; Refine ExIntro;
Next +1; Refine H1;
Save Lt_imp_Le;


Goal Lt_Le_resp_plus : {x,y,a,b:nat}(Lt x y) -> 
     (Le a b) -> (Lt (plus x a) (plus y b));
Intros x y a b h1 h2;
Refine Le_Lt_trans;
Refine +1 Le_resp_plus;
Refine +1 h2;
Qrepl plus_commutes x b;
Qrepl plus_commutes y b;
Refine Lt_resp_plus; Refine h1;
Save Lt_Le_resp_plus;


Goal Le_Lt_resp_plus : {x,y,a,b:nat}(Le x y) -> 
      (Lt a b) -> (Lt (plus x a) (plus y b));
Intros x y a b h1 h2;
Refine Lt_Le_trans;
Refine +1 Lt_resp_plus;
Refine +1 h2;
Qrepl plus_commutes x b;
Qrepl plus_commutes y b;
Refine Le_resp_plus; Refine h1;
Save Le_Lt_resp_plus;


Goal decide_nat : {x,y:nat}(or (Le x y) (Lt y x));
intros;
Refine nat_diagonal_ind [x,y:nat](or (Le x y) (Lt y x));
intros;
Refine inl;
Refine Le_zero_n;
intros;
Refine inr;
Refine zero_Lt_suc_n;
intros;
Refine H;
intros;
Refine inl;
Refine Le_resp_suc ? ? H1;
intros;
Refine inr;
Refine (Lt_resp_suc ? ?) H1;
Save decide_nat;


Goal Le_is_Lt_or_Eq : {x,y:nat}(Le x y) -> (or (Lt x y) (Eq x y));
intros;
Refine decide_nat y x;
intros;
Refine inr;
Refine Le_antisym;
Refine H1; Refine H;
intros; Refine inl; Refine H1;
Save Le_is_Lt_or_Eq;


Goal zero_or_pos : {n:nat}(Eq n zero)\/(Lt zero n);
intros;
Refine Le_is_Lt_or_Eq ?? (Le_zero_n n);
Refine inr;
intros;
Refine inl (Eq_sym H);
Save zero_or_pos;

Goal Lt_imp_Le_suc : {x,y:nat}(Lt x (suc y))->Le x y;
intros;
Refine H;
intros;
Refine ExIntro t;
Refine Eq_resp pred|(suc (plus x t))|(suc y);
Refine Eq_trans (Eq_sym (plus_suc ??)) H1;
Save Lt_imp_Le_suc;


Goal Le_imp_Lt_suc : {x,y:nat}(Le x y)->Lt x (suc y);
intros;
Refine H;
intros;
Refine ExIntro t;
Refine Eq_trans (plus_suc ??) (Eq_resp suc H1);
Save Le_imp_Lt_suc;


Goal Lt_resp_times_both : {x,y,a,b:nat}(Lt x y) -> (Lt a b) ->
  (Lt (times a x) (times b y));
intros;
Refine Le_Lt_trans;
Refine +1 Le_resp_times;
Refine +1 Lt_imp_Le;
Refine +1 H;
Qrepl times_commutes|a|y;
Qrepl times_commutes|b|y;
Refine H; intros;
Qrepl Eq_sym H2;
Qrepl plus_suc x t;
Refine Lt_resp_times;
Refine H1;
Save Lt_resp_times_both;

Goal {x,y:nat}(Lt x y)->Le (suc x) y;
intros;
Refine Lt_imp_Le_suc;
Refine Lt_resp_suc ?? H;
Save Lt_imp_Le_suc';


Goal {x,y:nat}(Le (suc x) y)->Lt x y;
intros;
Refine Lt_resp_pred;
Refine Le_imp_Lt_suc ?? H;
Save Le_imp_Lt_suc';

Goal minus_well_le : {m,n:nat}(Lt zero m)->(Le m n)->
              (Lt (plus (minus n m) m)) (plus n m);
intros;
Qrepl Eq_sym (plus_inv_minus ?? H1);
Refine Le_Lt_trans (eq_imp_Le ???) (Lt_resp_plus ??? H);
Refine Eq_sym (plus_zero|?); 
Save minus_well_le;


Goal not_Le_imp_Lt : {x,y:nat}(not (Le x y)) -> (Lt y x);
Refine nat_diagonal_ind [x,y:nat](not (Le x y)) -> (Lt y x);
intros;
Refine H;
Refine Le_zero_n;
intros;
Refine zero_Lt_suc_n;
intros;
Refine Lt_resp_suc;
Refine H;
Intros H2;
Refine H1;
Refine Le_resp_suc;
Refine H2;
Save not_Le_imp_Lt;


Goal not_Lt_imp_Le : {x,y:nat}(not (Lt x y)) -> (Le y x);
Refine nat_diagonal_ind [x,y:nat](not (Lt x y))->Le y x;
Refine nat_ind [m:nat](not (Lt zero m))->Le m zero;
intros;
Refine Le_zero_n;
intros;
Refine H1;
Refine zero_Lt_suc_n;
intros;
Refine Le_zero_n;
intros;
Refine Le_resp_suc;
Refine H;
Intros H2;
Refine H1;
Refine Lt_resp_suc;
Refine H2;
Save not_Lt_imp_Le;

Goal Le_minus_zero : {a,b:nat}(Le a b)->Eq (minus a b) zero;
Refine nat_ind[a:nat]{b:nat}(Le a b)->Eq (minus a b) zero;
intros;
Refine zero_minus_n_Eq_zero;
intros;
Refine ze_Lt_imp_Eq_suc b;
Refine Lt_Le_trans (zero_Lt_suc_n ?) H1;
intros;
Qrepl H2;
Qrepl (minus_resp_suc n t);
Refine H;
Refine Le_resp_pred;
Refine Eq_subst H2;
Refine H1;
Save Le_minus_zero;

Goal Le_resp_minus : {a,b,c:nat}(Le a b)->(Le (minus c b) (minus c a));
intros;
Refine decide_nat b c;
intros;
Refine Le_resp_sub ?? a;
Refine Eq_subst(plus_commutes|?|?);
Refine Eq_subst (plus_inv_minus ?? (Le_trans H H1));
Refine Eq_subst( Eq_sym (plus_inv_minus ?? H1));
Qrepl plus_commutes|a|(minus c b);
Refine Le_resp_plus ??? H;
intros;
Qrepl Le_minus_zero ?? (Lt_imp_Le ?? H1);
Refine Le_zero_n;
Save Le_resp_minus;
