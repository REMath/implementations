Module lib_nat_Le Import lib_nat_times_thms lib_nat_minus_thms;

(* Contents
   --------
   o A Prop-valued definition of the "less or equal" ordering on natural
     numbers.
   o Several theorems about this ordering.
*)

[Le = [n,m:nat] Ex [k:nat] Eq (plus n k) m : nat->nat->Prop];

Goal Le_plus_lemma1 : {m,n|nat}Le m (plus m n);
intros;exI ?;Refine +1 Eq_refl;
Save Le_plus_lemma1;


Goal Le_plus_lemma2 : {m,n|nat}Le n (plus m n);
intros;
Qrepl plus_commutes m n;
Refine Le_plus_lemma1;
Save Le_plus_lemma2;


Goal Le_suc_lemma : {m,n|nat}(Le m (suc n)) -> or (Le m n) (Eq (suc n) m);
intros;Refine H;
Refine nat_ind [t:nat](Eq (plus m t) (suc n))->or (Le m n) (Eq (suc n) m);
intros;Refine inr;Qrepl Eq_sym(plus_zero m);Refine Eq_sym H1;
intros;Refine inl;exI ?;Refine +1 suc_injective;
Refine n1;Qrepl Eq_sym H2;Refine Eq_sym;Refine plus_suc;
Save Le_suc_lemma;


Goal Le_antisym : {m,n:nat}(Le m n) -> (Le n m) -> (Eq n m);
Intros m n h1 h2;
Refine h1; Intros __;
Refine h2; Intros __;
Claim Eq t zero;
Qrepl Eq_sym H;
Qrepl ?+1;
Refine plus_zero;
Refine fst (plus_strict|?|? ?);
Refine t1;
Refine cancel_plus;
Refine n;
Qrepl (plus_zero n);
Qrepl plus_commutes t t1;
Qrepl Eq_sym (plus_assoc n t1 t);
Qrepl H1;
Refine H;
Save Le_antisym;


Goal Le_suc : {x:nat}Le x (suc x);
intros x;
Refine ExIntro;
Refine one;
Qrepl plus_commutes|x|one;
Refine Eq_refl;
Save Le_suc;

Goal Le_resp_suc : {x,y:nat}(Le x y) -> (Le (suc x) (suc y));
intros;
Refine H; intros;
Refine ExIntro;
Refine t;
Qrepl Eq_sym H1;
Refine Eq_refl;
Save Le_resp_suc;


Goal Le_resp_pred : {x,y:nat}(Le (suc x) (suc y)) -> (Le x y);
intros;
Refine H; intros;
Refine ExIntro;
Refine t;
Refine suc_injective;
Qrepl Eq_sym H1;
Refine Eq_refl;
Save Le_resp_pred;


Goal Le_zero_n : {n:nat}(Le zero n);
intros;Refine ExIntro; Refine n;
Refine Eq_refl;
Save Le_zero_n;

Goal Le_incl_pred : {x:nat}Le (pred x) x;
Refine nat_ind [x:nat]Le (pred x) x;
Refine Le_zero_n;
intros n ih;
Refine ExIntro;
Refine one;
Qrepl plus_commutes|n|one;
Refine Eq_refl;
Save Le_incl_pred;


Goal not_Le_zero_n : {n:nat}(not (Le (suc n) zero));
Intros n H;
Refine H; intros;
Refine zero_not_suc;
Refine plus n t;
Qrepl Eq_sym H1;
Refine Eq_refl;
Save not_Le_zero_n;

Goal Le_suc_pred : {a,b|nat}(Le (suc a) b) -> Le a (pred b);
Induction b;

  intros; Refine not_Le_zero_n; Immed;

  intros; Refine Le_resp_pred; Immed;
Save Le_suc_pred;


Goal eq_imp_Le : {x,y:nat}(Eq x y) -> (Le x y);
intros;
Refine ExIntro; Refine zero;
Qrepl H;
Refine plus_zero;
Save eq_imp_Le;


Goal Le_trans : {x,y,z|nat}(Le x y) -> (Le y z) ->(Le x z);
intros;
Refine H; intros;
Refine H1; intros;
Refine ExIntro;
Refine plus t t1;
Qrepl Eq_sym H3;
Qrepl Eq_sym H2;
Refine Eq_sym (plus_assoc ? ? ?);
Save Le_trans;


Goal Le_resp_plus : {x,y,z:nat}(Le x y) -> (Le (plus z x) (plus z y));
Intros x y z;
Refine nat_ind [z:nat](Le x y)->Le (plus z x) (plus z y);
intros; Refine H;
intros;
Refine Le_resp_suc;
Refine H;
Refine H1;
Save Le_resp_plus;


Goal Le_resp_sub : {x,y,z:nat}(Le (plus z x) (plus z y)) -> (Le x y);
Intros x y z;
Refine nat_ind [z:nat](Le (plus z x) (plus z y))->Le x y;
intros; Refine H;
intros;
Refine H;
Refine Le_resp_pred;
Refine H1;
Save Le_resp_sub;


Goal Le_resp_plus_both : {x,y,a,b:nat}(Le x y) -> 
(Le a b) -> (Le (plus x a) (plus y b));
Intros x y a b h1 h2;
Refine Le_trans;
Refine +1 Le_resp_plus;
Refine +1 h2;
Qrepl plus_commutes x b;
Qrepl plus_commutes y b;
Refine Le_resp_plus; Refine h1;
Save Le_resp_plus_both;


Goal Le_resp_times : {x,y,a:nat}(Le x y) -> 
  (Le (times a x) (times a y));
Intros x y a;
Refine nat_ind [a:nat]((Le x y)->Le (times a x) (times a y));
Intros H;
Refine eq_imp_Le;
Refine Eq_refl;
intros;
Refine Le_resp_plus_both;
Refine H1;
Refine H;
Refine H1;
Save Le_resp_times;


Goal Le_times_cancel : {x,y,a:nat}(Le (times x (suc a)) (times y (suc a)))
   -> (Le x y);
Intros x y a;
Refine nat_diagonal_ind [x,y:nat]((Le (times x (suc a)) (times y (suc a)))->Le x y);
intros;
Refine Le_zero_n;
intros;
Refine not_Le_zero_n;
Refine +1 H;
intros;
Refine Le_resp_suc;
Refine H;
Refine Le_resp_sub;
Refine +1 H1;
Save Le_times_cancel;


Goal Le_resp_times_both : {a,b,x,y:nat}(Le a b)->(Le x y)->Le (times a x) (times b y);
intros;
Refine Le_trans (Le_resp_times ??? H1);
Qrepl times_commutes|a|y;
Qrepl times_commutes|b|y;
Refine Le_resp_times ??? H;
Save Le_resp_times_both;



Goal plus_inv_minus : {m,n:nat}(Le m n)->(Eq n (plus (minus n m) m));
intros;
Refine H;
intros;
Qrepl Eq_sym H1;
Qrepl plus_commutes|m|t;
Refine Eq_resp [t:nat]plus t m;
Qrepl plus_commutes|t|m;
Refine minus_inv_plus;
Save plus_inv_minus;













