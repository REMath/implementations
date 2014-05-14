Module lib_int_Prop_rels Import lib_int_basics_thms 
				lib_nat_Prop_rels;

(* 
  $Log: lib_int_Prop_rels.l,v $
  Revision 1.3  1997/11/12 20:02:31  djs
  Fixed a "tms fixes it, CVS breaks it again" log message problem.

   Revision 1.2  1997/07/10 16:33:18  tms
   removed redundant Qrepl tactic
*)

Le_zed [a,b:int.1] == Le (plus a.1 b.2) (plus a.2 b.1);
Lt_zed [a,b:int.1] == Lt (plus a.1 b.2) (plus a.2 b.1);

Goal Le_resp_eq_l : {a,b,x:int.1}(eq a b) -> (Le_zed a x) -> (Le_zed b x);
intros;
Expand Le_zed;
Refine Le_resp_sub;
Refine a.2;
Qrepl Eq_sym(plus_assoc a.2 b.1 x.2);
Qrepl plus_commutes a.2 b.1;
Qrepl Eq_sym H;
Qrepl plus_commutes a.1 b.2;
Qrepl (plus_assoc b.2 a.1 x.2);
Qrepl Eq_sym(plus_assoc a.2 b.2 x.1);
Qrepl plus_commutes a.2 b.2;
Qrepl (plus_assoc b.2 a.2 x.1);
Refine Le_resp_plus;
Refine H1;
Save Le_resp_eq_l;

Goal Le_resp_eq_r : {a,b,x:int.1}(eq a b) -> (Le_zed x a) -> (Le_zed x b);
intros;
Expand Le_zed;
Refine Le_resp_sub;
Refine a.2;
Qrepl plus_commutes x.1 b.2;
Qrepl Eq_sym (plus_assoc a.2 b.2 x.1);
Qrepl plus_commutes a.2 b.2;
Qrepl (plus_assoc b.2 a.2 x.1);
Qrepl plus_commutes x.2 b.1;
Qrepl Eq_sym (plus_assoc a.2 b.1 x.2);
Qrepl plus_commutes a.2 b.1;
Qrepl Eq_sym H;
Qrepl plus_commutes a.1 b.2;
Qrepl (plus_assoc b.2 a.1 x.2);
Refine Le_resp_plus;
Qrepl plus_commutes a.2 x.1;
Qrepl plus_commutes a.1 x.2;
Refine H1;
Save Le_resp_eq_r;

Goal Lt_resp_eq_l : {a,b,x:int.1}(eq a b) -> (Lt_zed a x) -> (Lt_zed b x);
intros;
Expand Lt_zed;
Refine Lt_resp_sub;
Refine a.2;
Qrepl Eq_sym (plus_assoc a.2 b.1 x.2);
Qrepl plus_commutes a.2 b.1;
Qrepl Eq_sym H;
Qrepl plus_commutes a.1 b.2;
Qrepl (plus_assoc b.2 a.1 x.2);
Qrepl Eq_sym (plus_assoc a.2 b.2 x.1);
Qrepl plus_commutes a.2 b.2;
Qrepl (plus_assoc b.2 a.2 x.1);
Refine Lt_resp_plus;
Refine H1;
Save Lt_resp_eq_l;

Goal Lt_resp_eq_r : {a,b,x:int.1}(eq a b) -> (Lt_zed x a) -> (Lt_zed x b);
intros;
Expand Lt_zed;
Refine Lt_resp_sub;
Refine a.2;
Qrepl plus_commutes x.1 b.2;
Qrepl Eq_sym (plus_assoc a.2 b.2 x.1);
Qrepl plus_commutes a.2 b.2;
Qrepl (plus_assoc b.2 a.2 x.1);
Qrepl plus_commutes x.2 b.1;
Qrepl Eq_sym (plus_assoc a.2 b.1 x.2);
Qrepl plus_commutes a.2 b.1;
Qrepl Eq_sym H;
Qrepl plus_commutes a.1 b.2;
Qrepl (plus_assoc b.2 a.1 x.2);
Refine Lt_resp_plus;
Qrepl plus_commutes a.2 x.1;
Qrepl plus_commutes a.1 x.2;
Refine H1;
Save Lt_resp_eq_r;

Goal prod_pos_is_pos : {x,y:zed}(Lt_zed zero_zed x)
 -> (Lt_zed zero_zed y) -> (Lt_zed zero_zed (times_zed x y));
Expand Lt_zed zero_zed times_zed;
Intros x y;
Equiv (Lt x.2 x.1) -> (Lt y.2 y.1) 
->(Lt (plus (times ? ?) ?) (plus (times ? ?) ?));
Qrepl plus_commutes (times x.1 y.1) (times x.2 y.2);
Qrepl plus_commutes (times x.1 y.2) (times x.2 y.1);
Refine weird_Lt;
Save prod_pos_is_pos;

Goal pos_imp_non_zero : {x:int.1}(Lt_zed zero_zed x) -> not (eq x zero_zed);
intros;
Intros H1;
Refine not_refl_Lt;
Refine x.1;
Refine Eq_subst (Eq_sym(eq_zero_zed_imp ? (eq_sym_ax H1))) [t:nat]Lt t x.1;
Refine H;
Save pos_imp_non_zero;

Goal eq_imp_Le_zed : {x,y:int.1}(eq x y) -> (Le_zed x y);
intros;
Refine eq_imp_Le;
Refine Eq_subst (plus_commutes|?|?);
Refine H;
Save eq_imp_Le_zed;

(*
Goal {x,y:int.1}(Lt_zed x y) -> (Le_zed x y);
intros;
Refine Lt_imp_Le ? ? H;
*)
Goal Le_resp_times_zed : {x,y,z:int.1}(Le_zed x y) -> (Le_zed zero_zed z)
-> (Le_zed (times_zed z x) (times_zed z y));
intros;
Expand Le_zed times_zed;
Qrepl middle_four_plus|(times z.1 x.1)|(times z.1 y.2)|(times z.2 x.2)|(times z.2 y.1);
Qrepl middle_four_plus|(times z.1 x.2)|(times z.1 y.1)|(times z.2 x.1)|(times z.2 y.2);
Qrepl Eq_sym (times_plus_dist_l|z.1|x.1|y.2);
Qrepl Eq_sym (times_plus_dist_l|z.2|x.2|y.1);
Qrepl Eq_sym (times_plus_dist_l|z.1|x.2|y.1);
Qrepl Eq_sym (times_plus_dist_l|z.2|x.1|y.2);
Qrepl plus_commutes (times z.1 (plus x.1 y.2)) (times z.2 (plus x.2 y.1));
Qrepl plus_commutes (times z.1 (plus x.2 y.1)) (times z.2 (plus x.1 y.2));
Refine weird_Le;
Refine H1;
Refine H;
Save Le_resp_times_zed;

Goal Lt_resp_times_zed : {x,y,z:int.1}(Lt_zed x y) -> (Lt_zed zero_zed z)
-> (Lt_zed (times_zed z x) (times_zed z y));
intros;
Expand Lt_zed times_zed;
Qrepl middle_four_plus|(times z.1 x.1)|(times z.1 y.2)|(times z.2 x.2)|(times z.2 y.1);
Qrepl middle_four_plus|(times z.1 x.2)|(times z.1 y.1)|(times z.2 x.1)|(times z.2 y.2);
Qrepl Eq_sym (times_plus_dist_l|z.1|x.1|y.2);
Qrepl Eq_sym (times_plus_dist_l|z.2|x.2|y.1);
Qrepl Eq_sym (times_plus_dist_l|z.1|x.2|y.1);
Qrepl Eq_sym (times_plus_dist_l|z.2|x.1|y.2);
Qrepl plus_commutes (times z.1 (plus x.1 y.2)) (times z.2 (plus x.2 y.1));
Qrepl plus_commutes (times z.1 (plus x.2 y.1)) (times z.2 (plus x.1 y.2));
Refine weird_Lt;
Refine H1;
Refine H;
Save Lt_resp_times_zed;

Goal Le_times_cancel_left_zed : {x,y,a:int.1}(Lt_zed zero_zed a) ->
   (Le_zed (times_zed a x) (times_zed a y)) -> (Le_zed x y);
Intros x y z h1 h2;
Refine weird_thing_Le;
Refine +3 h1;
Expand Le_zed times_zed;
Qrepl times_plus_dist_l|z.2|x.2|y.1;
Qrepl times_plus_dist_l|z.1|x.1|y.2;
Qrepl times_plus_dist_l|z.2|x.1|y.2;
Qrepl times_plus_dist_l|z.1|x.2|y.1;
Qrepl middle_four_plus|(times z.2 x.2)|(times z.1 x.1)|(times z.2 y.1)|(times z.1 y.2);
Qrepl plus_commutes (times z.2 x.2) (times z.1 x.1);
Qrepl plus_commutes (times z.2 y.1) (times z.1 y.2);
Qrepl middle_four_plus|(times z.2 x.1)|(times z.1 x.2)|(times z.2 y.2)|(times z.1 y.1);
Qrepl plus_commutes (times z.2 x.1) (times z.1 x.2);
Qrepl plus_commutes (times z.2 y.2) (times z.1 y.1);
Refine h2;
Save Le_times_cancel_left_zed;

Goal Lt_times_cancel_left_zed : {x,y,a:int.1}(Lt_zed zero_zed a) ->
   (Lt_zed (times_zed a x) (times_zed a y)) -> (Lt_zed x y);
Intros x y z h1 h2;
Refine weird_thing_Lt;
Refine +3 h1;
Expand Lt_zed times_zed;
Qrepl times_plus_dist_l|z.2|x.2|y.1;
Qrepl times_plus_dist_l|z.1|x.1|y.2;
Qrepl times_plus_dist_l|z.2|x.1|y.2;
Qrepl times_plus_dist_l|z.1|x.2|y.1;
Qrepl middle_four_plus|(times z.2 x.2)|(times z.1 x.1)|(times z.2 y.1)|(times z.1 y.2);
Qrepl plus_commutes (times z.2 x.2) (times z.1 x.1);
Qrepl plus_commutes (times z.2 y.1) (times z.1 y.2);
Qrepl middle_four_plus|(times z.2 x.1)|(times z.1 x.2)|(times z.2 y.2)|(times z.1 y.1);
Qrepl plus_commutes (times z.2 x.1) (times z.1 x.2);
Qrepl plus_commutes (times z.2 y.2) (times z.1 y.1);
Refine h2;
Save Lt_times_cancel_left_zed;



Goal Lt_on_neg : {x,y:int.1}(Lt_zed x y) -> (Lt_zed (neg_zed y) (neg_zed x));
intros;
Expand neg_zed Lt_zed;
Qrepl plus_commutes y.2 x.1;
Qrepl plus_commutes y.1 x.2;
Refine H;
Save Lt_on_neg;

Goal Lt_on_neg_rev : {x,y:int.1}(Lt_zed (neg_zed y) (neg_zed x)) -> (Lt_zed x y);
intros;
Expand Lt_zed;
Qrepl plus_commutes x.2 y.1;
Qrepl plus_commutes x.1 y.2;
Refine H;
Save Lt_on_neg_rev;

Goal Le_on_neg : {x,y:int.1}(Le_zed x y) -> (Le_zed (neg_zed y) (neg_zed x));
intros;
Expand neg_zed Le_zed;
Qrepl plus_commutes y.2 x.1;
Qrepl plus_commutes y.1 x.2;
Refine H;
Save Le_on_neg;

Goal Le_on_neg_rev : {x,y:int.1}(Le_zed (neg_zed y) (neg_zed x)) -> (Le_zed x y);
intros;
Expand Le_zed;
Qrepl plus_commutes x.2 y.1;
Qrepl plus_commutes x.1 y.2;
Refine H;
Save Le_on_neg_rev;

Goal Le_antisym_zed : {x,y:int.1}(Le_zed x y) -> (Le_zed y x) -> (eq y x);
intros x y;
Expand Le_zed eq int eq_on_ints;
Expand Eq_zed;
intros;
Qrepl plus_commutes y.1 x.2;
Refine Le_antisym;
Refine H;
Qrepl plus_commutes x.2 y.1;
Qrepl plus_commutes x.1 y.2;
Refine H1;
Save Le_antisym_zed;

Goal Le_trans_zed : {x,y,z:int.1}(Le_zed x y) -> (Le_zed y z)
  -> Le_zed x z;
Expand Le_zed;
intros;
Refine Le_resp_sub;
Refine (plus y.2 y.1);
Qrepl middle_four_plus|y.2|x.1|y.1|z.2;
Qrepl plus_commutes y.2 x.1;
Qrepl plus_commutes y.2 y.1;
Qrepl middle_four_plus|y.1|x.2|y.2|z.1;
Refine Le_resp_plus_both;
Qrepl plus_commutes y.1 x.2;
Refine H;
Refine H1;
Save Le_trans_zed;

Goal not_refl_Lt_zed : {x:int.1}not (Lt_zed x x);
intros;
Intros H;
Refine not_refl_Lt;
Refine (plus x.1 x.2);
Refine Eq_subst (plus_commutes|?|?);
Refine H;
Save not_refl_Lt_zed;

Goal Lt_trans_zed : {x,y,z:int.1}(Lt_zed x y) -> (Lt_zed y z)
  -> Lt_zed x z;
Expand Le_zed Lt_zed;
intros;
Refine Lt_resp_sub;
Refine (plus y.2 y.1);
Qrepl middle_four_plus|y.2|x.1|y.1|z.2;
Qrepl plus_commutes y.2 x.1;
Qrepl plus_commutes y.2 y.1;
Qrepl middle_four_plus|y.1|x.2|y.2|z.1;
Refine Lt_resp_plus_both;
Qrepl plus_commutes y.1 x.2;
Refine H;
Refine H1;
Save Lt_trans_zed;

Goal Le_Lt_trans_zed : {x,y,z:int.1}(Le_zed x y) -> (Lt_zed y z)
  -> Lt_zed x z;
Expand Le_zed Lt_zed;
intros;
Refine Lt_resp_sub;
Refine (plus y.2 y.1);
Qrepl middle_four_plus|y.2|x.1|y.1|z.2;
Qrepl plus_commutes y.2 x.1;
Qrepl plus_commutes y.2 y.1;
Qrepl middle_four_plus|y.1|x.2|y.2|z.1;
Refine Le_Lt_resp_plus;
Qrepl plus_commutes y.1 x.2;
Refine H;
Refine H1;
Save Le_Lt_trans_zed;

Goal Lt_Le_trans_zed : {x,y,z:int.1}(Lt_zed x y) -> (Le_zed y z)
  -> Lt_zed x z;
Expand Le_zed Lt_zed;
intros;
Refine Lt_resp_sub;
Refine (plus y.2 y.1);
Qrepl middle_four_plus|y.2|x.1|y.1|z.2;
Qrepl plus_commutes y.2 x.1;
Qrepl plus_commutes y.2 y.1;
Qrepl middle_four_plus|y.1|x.2|y.2|z.1;
Refine Lt_Le_resp_plus;
Qrepl plus_commutes y.1 x.2;
Refine H;
Refine H1;
Save Lt_Le_trans_zed;

Goal Le_resp_plus_both_zed : {x,y,a,b:int.1}(Le_zed x y) -> (Le_zed a b)
 -> (Le_zed (plus_zed x a) (plus_zed y b));
Expand plus_zed Le_zed;
intros;
Qrepl middle_four_plus|x.1|y.2|a.1|b.2;
Qrepl middle_four_plus|x.2|y.1|a.2|b.1;
Refine Le_resp_plus_both;
Refine H;
Refine H1;
Save Le_resp_plus_both_zed;

Goal Lt_resp_plus_both_zed : {x,y,a,b:int.1}(Lt_zed x y) -> (Lt_zed a b)
 -> (Lt_zed (plus_zed x a) (plus_zed y b));
Expand plus_zed Lt_zed;
intros;
Qrepl middle_four_plus|x.1|y.2|a.1|b.2;
Qrepl middle_four_plus|x.2|y.1|a.2|b.1;
Refine Lt_resp_plus_both;
Refine H;
Refine H1;
Save Lt_resp_plus_both_zed;

Goal Lt_resp_plus_zed : {x,y,z:int.1}(Lt_zed x y)  -> 
(Lt_zed (plus_zed z x) (plus_zed z y));
Expand plus_zed Lt_zed;
intros;
Qrepl middle_four_plus|z.1|z.2|x.1|y.2;
Qrepl middle_four_plus|z.2|z.1|x.2|y.1;
Qrepl plus_commutes z.1 z.2;
Refine Lt_resp_plus;
Refine H;
Save Lt_resp_plus_zed;


Goal prod_Le_is_pos : {x,y:zed}(Le_zed zero_zed x)
 -> (Le_zed zero_zed y) -> (Le_zed zero_zed (times_zed x y));
Expand Le_zed zero_zed times_zed;
Intros x y;
Equiv (Le x.2 x.1) -> (Le y.2 y.1) 
->(Le (plus (times ? ?) ?) (plus (times ? ?) ?));
Qrepl plus_commutes (times x.1 y.1) (times x.2 y.2);
Qrepl plus_commutes (times x.1 y.2) (times x.2 y.1);
Refine weird_Le;
Save prod_Le_is_pos;

Goal decide_int : {x,y:int.1}(or (Le_zed x y) (Lt_zed y x));
Expand Le_zed Lt_zed;
intros;
Qrepl plus_commutes y.1 x.2;
Qrepl plus_commutes y.2 x.1;
Refine decide_nat;
Save decide_int;

Goal Le_is_Lt_or_Eq_zed : {x,y:int.1}(Le_zed x y) -> (or (Lt_zed x y) (eq x y));
Expand Le_zed Lt_zed eq int Eq_zed;
intros;
Qrepl plus_commutes y.1 x.2;
Refine Le_is_Lt_or_Eq;
Refine H;
Save Le_is_Lt_or_Eq_zed;


Goal Le_resp_times_zed_neg : {x,y,z:int.1}(Le_zed x y) -> (Lt_zed z zero_zed)
-> (Le_zed (times_zed z y) (times_zed z x));
intros;
Expand Le_zed times_zed;
Qrepl middle_four_plus|(times z.1 y.1)|(times z.1 x.2)|(times z.2 y.2)|(times z.2 x.1);
Qrepl middle_four_plus|(times z.1 y.2)|(times z.1 x.1)|(times z.2 y.1)|(times z.2 x.2);
Qrepl Eq_sym (times_plus_dist_l|z.1|y.1|x.2);
Qrepl Eq_sym (times_plus_dist_l|z.2|y.2|x.1);
Qrepl Eq_sym (times_plus_dist_l|z.1|y.2|x.1);
Qrepl Eq_sym (times_plus_dist_l|z.2|y.1|x.2);
Qrepl plus_commutes (times z.1 (plus y.1 x.2)) (times z.2 (plus y.2 x.1));
Qrepl plus_commutes (times z.1 (plus y.2 x.1)) (times z.2 (plus y.1 x.2));
Qrepl plus_commutes y.2 x.1;
Qrepl plus_commutes y.1 x.2;
Qrepl times_commutes|z.2|(plus x.1 y.2);
Qrepl times_commutes|z.1|(plus x.2 y.1);
Qrepl times_commutes|z.2|(plus x.2 y.1);
Qrepl times_commutes|z.1|(plus x.1 y.2);
Qrepl plus_commutes (times (plus x.2 y.1) z.2) (times (plus x.1 y.2) z.1);
Refine weird_Le;
Refine H;
Refine Lt_imp_Le;
Qrepl Eq_sym (plus_zero z.1);
Qrepl Eq_sym (plus_zero z.2);
Refine H1;
Save Le_resp_times_zed_neg;
