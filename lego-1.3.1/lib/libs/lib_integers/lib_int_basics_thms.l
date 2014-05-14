Module lib_int_basics_thms Import lib_int_basics;

Goal times_one_zed : {m|int.1}eq m (times_zed one_zed m);
intros;Expand eq times_zed; 
Qrepl(Eq_sym(times_one|m.1));
Qrepl(Eq_sym(times_one|m.2));
Qrepl plus_zero m.2;
Qrepl plus_zero m.1;
Refine Eq_refl;
Save times_one_zed;

Goal middle_four_plus_zed : {a,b,c,d|int.1}eq (plus_zed (plus_zed a c) (plus_zed b d)) (plus_zed (plus_zed a b) (plus_zed c d));
Expand eq int plus_zed; intros;
Qrepl middle_four_plus|a.1|b.1|c.1|d.1;
Qrepl middle_four_plus|a.2|b.2|c.2|d.2;Refine Eq_refl;
Save middle_four_plus_zed;

Goal times_plus_dist_r_zed : {a,b,c|int.1}eq (times_zed (plus_zed a b) c) (plus_zed (times_zed a c) (times_zed b c));
intros;
Expand times_zed plus_zed;
Expand eq int;
Qrepl times_plus_dist_r|a.1|b.1|c.1;
Qrepl times_plus_dist_r|a.1|b.1|c.2;
Qrepl times_plus_dist_r|a.2|b.2|c.1;
Qrepl times_plus_dist_r|a.2|b.2|c.2;
Qrepl middle_four_plus|(times a.1 c.1)|(times b.1 c.1)|(times a.2 c.2)|(times b.2 c.2);
Qrepl middle_four_plus|(times a.1 c.2)|(times b.1 c.2)|(times a.2 c.1)|(times b.2 c.1);
Refine Eq_refl;
Save times_plus_dist_r_zed;

Goal times_plus_dist_l_zed : {a,b,c|int.1}eq (times_zed c (plus_zed a b)) (plus_zed (times_zed c a) (times_zed c b));
intros b c a;Expand eq plus_zed times_zed;
Qrepl times_plus_dist_l|a.1|b.1|c.1;
Qrepl times_plus_dist_l|a.1|b.2|c.2;
Qrepl times_plus_dist_l|a.2|b.1|c.1;
Qrepl times_plus_dist_l|a.2|b.2|c.2;
Qrepl middle_four_plus|(times a.1 b.1)|(times a.2 b.2)|(times a.1 c.1)|(times a.2 c.2);
Qrepl middle_four_plus|(times a.1 b.2)|(times a.2 b.1)|(times a.1 c.2)|(times a.2 c.1);
Refine Eq_refl;
Save times_plus_dist_l_zed;

Goal times_resp_eq_l : {a,b,x:int.1}(eq a b) -> (eq (times_zed x a) (times_zed x b));
intros;
Expand eq int Eq_zed times_zed;
Refine Eq_trans;
Refine +1 middle_four_plus;
Qrepl (Eq_sym (times_plus_dist_l|x.1|a.1|b.2));
Qrepl (Eq_sym (times_plus_dist_l|x.2|a.2|b.1));
Refine Eq_trans;
Refine +2 middle_four_plus;
Qrepl (Eq_sym (times_plus_dist_l|x.1|b.1|a.2));
Qrepl (Eq_sym (times_plus_dist_l|x.2|b.2|a.1));
Qrepl plus_commutes a.2 b.1;
Qrepl plus_commutes b.2 a.1;
Qrepl H;
Refine Eq_refl;
Save times_resp_eq_l;

(* commutativity of plus_zed !!! *)
Goal plus_commutes_zed : {p,q|int.1}Eq (plus_zed p q) (plus_zed q p);
intros;Expand plus_zed;
Qrepl (plus_commutes |p.1 |q.1);
Qrepl (plus_commutes |p.2 |q.2);
Refine Eq_refl;
Save plus_commutes_zed;

(* commutativity of times_zed !!! *)
Goal times_commutes_zed : {p,q|int.1}Eq (times_zed p q) (times_zed q p);
intros;Expand times_zed;
Qrepl (times_commutes |p.1 |q.1);
Qrepl (times_commutes |p.2 |q.2);
Qrepl (times_commutes |p.2 |q.1);
Qrepl (times_commutes |q.2 |p.1);
Qrepl (plus_commutes |(times p.1 q.2) |(times q.1 p.2));
Refine Eq_refl;
Save times_commutes_zed;

Goal times_assoc_zed : {a,b,c|int.1}eq (times_zed (times_zed a b) c) (times_zed a (times_zed b c));
intros;Expand eq times_zed; 
Expand int Eq_zed;

(* distributivity *)
Qrepl times_plus_dist_r|(times a.1 b.1)|(times a.2 b.2)|c.1;
Qrepl times_plus_dist_r|(times a.1 b.2)|(times a.2 b.1)|c.2;
Qrepl times_plus_dist_l|a.1|(times b.1 c.2)|(times b.2 c.1);
Qrepl times_plus_dist_l|a.2|(times b.1 c.1)|(times b.2 c.2);
Qrepl times_plus_dist_l|a.1|(times b.1 c.1)|(times b.2 c.2);
Qrepl times_plus_dist_l|a.2|(times b.1 c.2)|(times b.2 c.1);
Qrepl times_plus_dist_r|(times a.1 b.1)|(times a.2 b.2)|c.2;
Qrepl times_plus_dist_r|(times a.1 b.2)|(times a.2 b.1)|c.1;

(* permutation *)
Qrepl plus_commutes (times a.2 (times b.1 c.2)) (times a.2 (times b.2 c.1));
Qrepl middle_four_plus|(times a.1 (times b.1 c.1))|(times a.2 (times b.2 c.1))
                     |(times a.1 (times b.2 c.2))|(times a.2 (times b.1 c.2));
Qrepl middle_four_plus|(times (times a.1 b.1) c.2)|(times (times a.1 b.2) c.1)
                     |(times (times a.2 b.2) c.2)|(times (times a.2 b.1) c.1);
Qrepl plus_commutes (times (times a.2 b.2) c.2) (times (times a.2 b.1) c.1);

(* associativity *)
Qrepl times_assoc|a.1|b.1|c.1;
Qrepl times_assoc|a.2|b.2|c.1;
Qrepl times_assoc|a.1|b.2|c.2;
Qrepl times_assoc|a.2|b.1|c.2;
Qrepl times_assoc|a.1|b.1|c.2;
Qrepl times_assoc|a.2|b.2|c.2;
Qrepl times_assoc|a.1|b.2|c.1;
Qrepl times_assoc|a.2|b.1|c.1;

Refine Eq_refl;

Save times_assoc_zed;

Goal plus_resp_eq : {a,b,x,y:int.1}(eq a b) -> (eq x y) ->
                 (eq (plus_zed a x) (plus_zed b y));
intros;
Refine Eq_trans;
Refine +1 middle_four_plus;
Refine Eq_trans;
Refine +2 middle_four_plus;
Qrepl H;
Qrepl H1;
Refine Eq_refl;
Save plus_resp_eq;

Goal minus_resp_eq : {a,b,x,y:int.1}(eq a b) -> (eq x y) ->
                 (eq (minus_zed a x) (minus_zed b y));
intros;
Refine Eq_trans;
Refine +1 middle_four_plus;
Refine Eq_trans;
Refine +2 middle_four_plus;
Qrepl H;
Qrepl (plus_commutes x.2 y.1);
Qrepl (Eq_sym H1);
Qrepl (plus_commutes x.1 y.2);
Refine Eq_refl;
Save minus_resp_eq;


(* Multiplication is hard, do one side at a time *)

Goal times_resp_eq_r : {a,b,x:int.1}(eq a b) -> (eq (times_zed a x) (times_zed b x));
intros;
Expand eq int Eq_zed times_zed;
Qrepl (plus_commutes (times b.1 x.2) (times b.2 x.1));
Refine Eq_trans;
Refine +1 middle_four_plus;
Qrepl (Eq_sym (times_plus_dist_r|a.1|b.2|x.1));
Qrepl (Eq_sym (times_plus_dist_r|a.2|b.1|x.2));
Qrepl (plus_commutes (times a.1 x.2) (times a.2 x.1));
Refine Eq_trans;
Refine +2 middle_four_plus;
Qrepl (Eq_sym (times_plus_dist_r|b.1|a.2|x.1));
Qrepl (Eq_sym (times_plus_dist_r|b.2|a.1|x.2));
Qrepl plus_commutes a.2 b.1;
Qrepl plus_commutes b.2 a.1;
Qrepl H;
Refine Eq_refl;
Save times_resp_eq_r;

Goal times_resp_eq : {a,b,x,y:int.1}(eq a b) -> (eq x y) ->
                 (eq (times_zed a x) (times_zed b y));
intros;
Refine eq_trans_ax;
Refine +1 times_resp_eq_l;
Refine +1 H1;
Refine times_resp_eq_r;
Refine H;
Save times_resp_eq;
(* Easy *)


Goal neg_resp_eq : {x,y:int.1}(eq x y) -> (eq (neg_zed x) (neg_zed y));
intros;
Refine Eq_sym;
Qrepl plus_commutes y.2 x.1;
Qrepl plus_commutes x.2 y.1;
Refine H;
Save neg_resp_eq;


(* Have now shown that all operations respect equality *)

Goal neg_minus : {x,y:int.1}(eq (plus_zed x (neg_zed y)) (minus_zed x y));
intros;
Refine Eq_refl;
Save neg_minus;    (* Isn't life wonderful  *)


Goal times_cancel_left_zed : {x,y,a:int.1}(not (eq a zero_zed)) ->
   (eq (times_zed a x) (times_zed a y)) -> (eq x y);
Intros x y z h1 h2;
Refine weird_thing;
Refine z.1; Refine z.2; Refine (plus x.1 y.2);
Refine (plus y.1 x.2);
Qrepl times_plus_dist_l|z.1|x.1|y.2;
Qrepl times_plus_dist_l|z.2|y.1|x.2;
Qrepl times_plus_dist_l|z.1|y.1|x.2;
Qrepl times_plus_dist_l|z.2|x.1|y.2;
Qrepl plus_commutes (times z.2 y.1) (times z.2 x.2);
Refine Eq_trans; Refine +1 middle_four_plus;
Qrepl plus_commutes (times z.2 x.1) (times z.2 y.2);
Refine Eq_trans; Refine +2 Eq_sym; Refine +2 middle_four_plus;
Refine h2;
Intros h3; Refine h1; Refine Eq_subst h3;
Refine plus_zero;
Intros h3; Refine h3;
Save times_cancel_left_zed;


Goal middle_four_times_zed : {x,y,a,b:int.1} (eq (times_zed (times_zed x y) (times_zed a b)) 
(times_zed (times_zed x a) (times_zed y b)));
Intros x y a b;
Refine eq_trans_ax;
Refine +1 times_assoc_zed;
Refine eq_trans_ax;
Refine +2 eq_sym_ax;
Refine +2 times_assoc_zed;
Refine times_resp_eq_l;
Refine eq_trans_ax;
Refine +2 times_assoc_zed;
Refine eq_trans_ax;
Refine +1 eq_sym_ax;
Refine +1 times_assoc_zed;
Refine times_resp_eq_r;
Refine Eq_subst (times_commutes_zed|?|?);
Refine eq_refl_ax;
Save middle_four_times_zed;

Goal eq_zero_zed_imp : {x:zed}(eq zero_zed x) -> (Eq x.1 x.2);
Intros x h1;
Refine Eq_sym;
Refine Eq_subst (plus_zero|?);
Refine h1;
Save eq_zero_zed_imp;

Goal imp_eq_zero_zed : {x:zed}(Eq x.1 x.2) -> (eq zero_zed x);
intros;
Refine Eq_subst (Eq_sym (plus_zero ?));
Refine Eq_sym H;
Save imp_eq_zero_zed;

Goal times_zero_lemma_zed : {x,y:zed}(eq (times_zed x y) (zero_zed)) -> (or
      (eq zero_zed x) (eq zero_zed y));
intros;
Refine weird_thing  x.1 x.2 y.1 y.2;
Refine eq_zero_zed_imp ? (eq_sym_ax H);
intros;
Refine inl;
Refine imp_eq_zero_zed;
Refine H1;
intros;
Refine inr;
Refine imp_eq_zero_zed;
Refine H1;
Save times_zero_lemma_zed;


(* Need distributivity for subtraction *)
Goal right_dist_minus_times_zed : {a,b,c|int.1}eq (times_zed (minus_zed a b) c) (minus_zed (times_zed a c) (times_zed b c));
intros;Expand eq minus_zed times_zed;
Qrepl times_plus_dist_r|a.1|b.2|c.1;
Qrepl times_plus_dist_r|a.2|b.1|c.2;
Qrepl times_plus_dist_r|a.2|b.1|c.1;
Qrepl times_plus_dist_r|a.1|b.2|c.2;
Qrepl middle_four_plus|(times a.1 c.1)|(times a.2 c.2)|(times b.2 c.1)|(times b.1 c.2);
Qrepl plus_commutes (times b.1 c.2) (times b.2 c.1);
Qrepl middle_four_plus|(times a.1 c.2)|(times a.2 c.1)|(times b.2 c.2)|(times b.1 c.1);
Qrepl plus_commutes (times b.1 c.1) (times b.2 c.2);
Refine Eq_refl;
Save right_dist_minus_times_zed;


Goal times_neg : {x,y:int.1}(eq (times_zed x (neg_zed y)) (times_zed y (neg_zed x)));
intros;
Expand times_zed neg_zed eq int Eq_zed;
Qrepl times_commutes|x.1|y.2;
Qrepl times_commutes|x.2|y.1;
Qrepl times_commutes|x.1|y.1;
Qrepl times_commutes|x.2|y.2;
Qrepl plus_commutes (times y.2 x.1) (times y.1 x.2);
Refine Eq_refl;
Save times_neg;

Goal times_neg_both : {x,y:int.1}(eq (times_zed x y) (times_zed (neg_zed x) (neg_zed y)));
intros;
Expand times_zed neg_zed eq int Eq_zed;
Qrepl plus_commutes (times x.2 y.2) (times x.1 y.1);
Qrepl plus_commutes (times x.1 y.2) (times x.2 y.1);
Refine Eq_refl;
Save times_neg_both;

Goal plus_assoc_zed : {a,b,c|int.1}eq (plus_zed (plus_zed a b) c) (plus_zed a (plus_zed b c));
intros;
Expand eq int Eq_zed plus_zed;
Qrepl Eq_sym(plus_assoc a.1 b.1 c.1);
Qrepl Eq_sym(plus_assoc a.2 b.2 c.2);
Refine Eq_refl;
Save plus_assoc_zed;

Goal one_times_zed : {x:int.1}(eq (times_zed one_zed x) x);
intros;
Expand one_zed times_zed;
Qrepl Eq_sym (times_one|x.1);
Qrepl Eq_sym (times_one|x.2);
Qrepl times_commutes|zero|x.2;
Qrepl times_commutes|zero|x.1;
Qrepl Eq_sym (times_zero|x.1);
Qrepl Eq_sym (times_zero|x.2);
Qrepl (plus_zero x.1);
Qrepl (plus_zero x.2);
Refine Eq_refl;
Save one_times_zed;

Goal plus_zero_zed : {x:int.1}(eq (plus_zed x zero_zed) x);
intros;
Expand zero_zed plus_zed;
Qrepl (plus_zero x.1);
Qrepl (plus_zero x.2);
Refine Eq_refl;
Save plus_zero_zed;

Goal minus_zed_is : {x,y,z:int.1}iff (eq (minus_zed x y) z) (eq x (plus_zed y z));
intros;
Refine pair;
Expand eq int Eq_zed minus_zed plus_zed;
intros;
Qrepl Eq_sym(plus_assoc x.1 y.2 z.2);
Qrepl H;
Qrepl plus_commutes x.2 y.1;
Qrepl Eq_sym(plus_assoc z.1 y.1 x.2);
Qrepl plus_commutes z.1 y.1;
Refine Eq_refl;
Expand eq int Eq_zed minus_zed plus_zed;
intros;
Qrepl (plus_assoc x.1 y.2 z.2);
Qrepl H;
Qrepl plus_commutes y.1 z.1;
Qrepl (plus_assoc z.1 y.1 x.2);
Qrepl plus_commutes y.1 x.2;
Refine Eq_refl;
Save minus_zed_is;

Goal n_minus_n_Eq_zero_zed : {x:int.1}(eq (minus_zed x x) zero_zed);
intros;
Expand eq int Eq_zed minus_zed zero_zed;
Qrepl plus_commutes x.1 x.2;
Refine Eq_sym;
Refine Eq_sym (plus_zero ?);
Save n_minus_n_Eq_zero_zed;


Goal plus_inv_minus_zed : {x,y:int.1}(eq (plus_zed (minus_zed x y) y) x);
intros;
Expand plus_zed minus_zed eq int Eq_zed;
Qrepl plus_commutes x.2 y.1;
Qrepl (plus_assoc y.1 x.2 y.2);
Qrepl plus_commutes x.2 y.2;
Qrepl Eq_sym(plus_assoc y.1 y.2 x.2);
Qrepl plus_commutes y.1 y.2;
Qrepl Eq_sym(plus_assoc x.1 (plus y.2 y.1) x.2);
Qrepl Eq_sym(plus_assoc x.1 y.2 y.1);
Refine Eq_refl;
Save plus_inv_minus_zed;


Goal bring_neg_out : {x,y:int.1}(eq (times_zed (neg_zed x) y) (neg_zed (times_zed x y)));
intros;
Expand eq int Eq_zed times_zed neg_zed;
Qrepl plus_commutes (times x.2 y.1) (times x.1 y.2);
Qrepl plus_commutes (times x.1 y.1) (times x.2 y.2);
Refine Eq_refl;
Save bring_neg_out;



Goal minus_is_minus_zed : {a,b:nat}(Le a b)->eq (minus_zed (b,zero) (a,zero)) (minus b a,zero);
intros;
Refine Eq_subst (plus_inv_minus ?? H);
Qrepl (plus_zero|b);
Refine (plus_zero|b);
Save minus_is_minus_zed;

