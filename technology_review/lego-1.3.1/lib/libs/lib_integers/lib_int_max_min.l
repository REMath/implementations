Module lib_int_max_min Import lib_int_basics_thms
                              lib_int_Prop_rels
                              lib_max_min;
(* Time-stamp: <01 Aug 95 tms ~/library/new/lib_all/lib_int_max_min.l> *)

min_zed [a,b:int.1] == ((min (plus a.1 b.2) (plus a.2 b.1)),
      (plus a.2 b.2)):int.1;
max_zed [a,b:int.1] == ((max (plus a.1 b.2) (plus a.2 b.1)),
      (plus a.2 b.2)):int.1;


Goal max_resp_eq : {a,b,x,y:int.1}(eq a b) -> (eq x y) ->
                 (eq (max_zed a x) (max_zed b y));
intros;
Expand eq int Eq_zed max_zed;
Qrepl (Eq_sym (max_resp_plus (plus a.1 x.2) (plus a.2 x.1) (plus b.2 y.2)));
Qrepl (Eq_sym (max_resp_plus (plus b.1 y.2) (plus b.2 y.1) (plus a.2 x.2)));
Qrepl middle_four_plus|a.1|b.2|x.2|y.2;
Qrepl middle_four_plus|a.2|b.2|x.1|y.2;
Qrepl middle_four_plus|b.1|a.2|y.2|x.2;
Qrepl middle_four_plus|b.2|a.2|y.1|x.2;
Qrepl plus_commutes a.2 b.2;
Qrepl plus_commutes x.2 y.2;
Qrepl H;
Qrepl H1;
Refine Eq_refl;
Save max_resp_eq;

Goal min_resp_eq : {a,b,x,y:int.1}(eq a b) -> (eq x y) ->
                 (eq (min_zed a x) (min_zed b y));
intros;
Expand eq int Eq_zed min_zed;
Qrepl (Eq_sym (min_resp_plus (plus a.1 x.2) (plus a.2 x.1) (plus b.2 y.2)));
Qrepl (Eq_sym (min_resp_plus (plus b.1 y.2) (plus b.2 y.1) (plus a.2 x.2)));
Qrepl middle_four_plus|a.1|b.2|x.2|y.2;
Qrepl middle_four_plus|a.2|b.2|x.1|y.2;
Qrepl middle_four_plus|b.1|a.2|y.2|x.2;
Qrepl middle_four_plus|b.2|a.2|y.1|x.2;
Qrepl plus_commutes a.2 b.2;
Qrepl plus_commutes x.2 y.2;
Qrepl H;
Qrepl H1;
Refine Eq_refl;
Save min_resp_eq;



Goal max_Le_left_zed : {x,y:int.1}(Le_zed x (max_zed x y));
intros;
Expand max_zed Le_zed;
Qrepl plus_commutes x.2 (max (plus x.1 y.2) (plus x.2 y.1));
Qrepl Eq_sym (max_resp_plus|(plus x.1 y.2)|(plus x.2 y.1)|x.2);
Qrepl plus_commutes x.2 y.2;
Qrepl Eq_sym (plus_assoc x.1 y.2 x.2);
Refine max_Le_left;
Save max_Le_left_zed;

Goal max_Le_right_zed : {x,y:int.1}(Le_zed y (max_zed x y));
intros;
Expand max_zed Le_zed;
Qrepl plus_commutes y.2 (max (plus x.1 y.2) (plus x.2 y.1));
Qrepl Eq_sym (max_resp_plus|(plus x.1 y.2)|(plus x.2 y.1)|y.2);
Qrepl plus_commutes x.2 y.1;
Qrepl Eq_sym (plus_assoc y.1 x.2 y.2);
Refine max_Le_right;
Save max_Le_right_zed;

Goal min_Le_left_zed : {x,y:int.1}(Le_zed (min_zed x y) x);
intros;
Expand min_zed Le_zed;
Qrepl Eq_sym (min_resp_plus|(plus x.1 y.2)|(plus x.2 y.1)|x.2);
Qrepl plus_commutes (plus x.1 y.2) x.2;
Qrepl plus_commutes x.1 y.2;
Qrepl Eq_sym (plus_assoc x.2 y.2 x.1);
Refine min_Le_right;
Save min_Le_left_zed;

Goal min_Le_right_zed : {x,y:int.1}(Le_zed (min_zed x y) y);
intros;
Expand min_zed Le_zed;
Qrepl Eq_sym (min_resp_plus|(plus x.1 y.2)|(plus x.2 y.1)|y.2);
Qrepl plus_commutes (plus x.2 y.1) y.2;
Qrepl Eq_sym (plus_assoc y.2 x.2 y.1);
Qrepl plus_commutes y.2 x.2;
Refine min_Le_left;
Save min_Le_right_zed;

Goal max_is_least_zed : {x,y,z:int.1}(Le_zed x z) -> (Le_zed y z) -> (Le_zed (max_zed x y) z);
Expand max_zed Le_zed;
intros;
Qrepl Eq_sym (max_resp_plus|(plus x.1 y.2)|(plus x.2 y.1)|z.2);
Refine max_is_least;
Qrepl plus_commutes x.1 y.2;
Qrepl plus_commutes x.2 y.2;
Qrepl (plus_assoc y.2 x.1 z.2);
Qrepl (plus_assoc y.2 x.2 z.1);
Refine Le_resp_plus;
Refine H;
Qrepl (plus_assoc x.2 y.1 z.2);
Qrepl (plus_assoc x.2 y.2 z.1);
Refine Le_resp_plus;
Refine H1;
Save max_is_least_zed;

Goal min_is_greatest_zed : {x,y,z:int.1}(Le_zed z x) -> (Le_zed z y) -> (Le_zed z (min_zed x y));
Expand min_zed Le_zed;
intros;
Qrepl plus_commutes z.2 (min (plus x.1 y.2) (plus x.2 y.1));
Qrepl Eq_sym (min_resp_plus|(plus x.1 y.2)|(plus x.2 y.1)|z.2);
Refine min_is_greatest;
Qrepl Eq_sym (plus_assoc z.1 x.2 y.2);
Qrepl plus_commutes (plus z.1 x.2) y.2;
Qrepl plus_commutes x.1 y.2;
Qrepl (plus_assoc y.2 x.1 z.2);
Refine Le_resp_plus;
Qrepl plus_commutes x.1 z.2;
Refine H;
Qrepl Eq_sym (plus_assoc z.1 x.2 y.2);
Qrepl plus_commutes z.1 x.2;
Qrepl (plus_assoc x.2 z.1 y.2);
Qrepl (plus_assoc x.2 y.1 z.2);
Qrepl plus_commutes y.1 z.2;
Refine Le_resp_plus;
Refine H1;
Save min_is_greatest_zed;

Goal max_resp_plus_zed : {x,y,z:int.1}(eq (max_zed (plus_zed z x) (plus_zed z y)) 
    (plus_zed z (max_zed x y)));
intros;
Expand max_zed plus_zed eq int Eq_zed;
Qrepl plus_commutes z.1 (max (plus x.1 y.2) (plus x.2 y.1));
Qrepl Eq_sym (max_resp_plus|(plus x.1 y.2)|(plus x.2 y.1)|z.1);
Qrepl plus_commutes z.2 y.2;
Qrepl plus_commutes z.2 x.2;
Qrepl middle_four_plus|x.2|z.1|z.2|y.1;
Qrepl plus_commutes z.2 y.1;
Qrepl Eq_sym (plus_assoc (plus z.1 x.1) y.2 z.2);
Qrepl Eq_sym (plus_assoc (plus x.2 z.1) y.1 z.2);
Qrepl max_resp_plus|(plus (plus z.1 x.1) y.2)|(plus (plus x.2 z.1) y.1)|z.2;
Refine Eq_trans;
Refine +1 (plus_assoc ? ? ?);
Qrepl Eq_sym(plus_assoc z.2 z.2 (plus x.2 y.2));
Qrepl middle_four_plus|z.2|x.2|z.2|y.2;
Qrepl plus_commutes z.2 x.2;
Qrepl plus_commutes z.2 y.2;
Qrepl plus_commutes x.1 y.2;
Qrepl plus_commutes(plus z.1 x.1) y.2;
Qrepl plus_commutes z.1 x.1;
Qrepl Eq_sym (plus_assoc y.2 x.1 z.1);
Qrepl (plus_assoc x.2 y.1 z.1);
Qrepl plus_commutes y.1 z.1;
Qrepl Eq_sym (plus_assoc x.2 z.1 y.1);
Refine Eq_refl;
Save max_resp_plus_zed;

Goal min_resp_plus_zed : {x,y,z:int.1}(eq (min_zed (plus_zed z x) (plus_zed z y)) 
    (plus_zed z (min_zed x y)));
intros;
Expand min_zed plus_zed eq int Eq_zed;
Qrepl plus_commutes z.1 (min (plus x.1 y.2) (plus x.2 y.1));
Qrepl Eq_sym (min_resp_plus|(plus x.1 y.2)|(plus x.2 y.1)|z.1);
Qrepl plus_commutes z.2 y.2;
Qrepl plus_commutes z.2 x.2;
Qrepl middle_four_plus|x.2|z.1|z.2|y.1;
Qrepl plus_commutes z.2 y.1;
Qrepl Eq_sym (plus_assoc (plus z.1 x.1) y.2 z.2);
Qrepl Eq_sym (plus_assoc (plus x.2 z.1) y.1 z.2);
Qrepl min_resp_plus|(plus (plus z.1 x.1) y.2)|(plus (plus x.2 z.1) y.1)|z.2;
Refine Eq_trans;
Refine +1 (plus_assoc ? ? ?);
Qrepl Eq_sym (plus_assoc z.2 z.2 (plus x.2 y.2));
Qrepl middle_four_plus|z.2|x.2|z.2|y.2;
Qrepl plus_commutes z.2 x.2;
Qrepl plus_commutes z.2 y.2;
Qrepl plus_commutes x.1 y.2;
Qrepl plus_commutes (plus z.1 x.1) y.2;
Qrepl plus_commutes z.1 x.1;
Qrepl Eq_sym (plus_assoc y.2 x.1 z.1);
Qrepl (plus_assoc x.2 y.1 z.1);
Qrepl plus_commutes y.1 z.1;
Qrepl Eq_sym (plus_assoc x.2 z.1 y.1);
Refine Eq_refl;
Save min_resp_plus_zed;

(*
Goal {x,y,z:int.1}(eq (min_zed (plus_zed z x) (plus_zed z y)) 
    (plus_zed z (min_zed x y)));
Solved ????
*)

(* Alternative stuff for max and min *)

Goal Le_min_left_zed : {x,y:int.1}(Le_zed x y) -> (eq (min_zed x y) x);
intros;
Refine Le_antisym_zed;
Refine min_is_greatest_zed;
Refine eq_imp_Le_zed;
Refine eq_refl_ax;
Refine H;
Refine min_Le_left_zed;
Save Le_min_left_zed;

Goal Le_min_right_zed : {x,y:int.1}(Le_zed y x) -> (eq (min_zed x y) y);
intros;
Refine Le_antisym_zed;
Refine min_is_greatest_zed;
Refine H;
Refine eq_imp_Le_zed;
Refine eq_refl_ax;
Refine min_Le_right_zed;
Save Le_min_right_zed;

Goal Le_max_right_zed : {x,y:int.1}(Le_zed x y) -> (eq (max_zed x y) y);
intros;
Refine Le_antisym_zed;
Refine max_Le_right_zed;
Refine max_is_least_zed;
Refine H;
Refine eq_imp_Le_zed;
Refine eq_refl_ax;
Save Le_max_right_zed;

Goal Le_max_left_zed : {x,y:int.1}(Le_zed y x) -> (eq (max_zed x y) x);
intros;
Refine Le_antisym_zed;
Refine max_Le_left_zed;
Refine max_is_least_zed;
Refine eq_imp_Le_zed;
Refine eq_refl_ax;
Refine H;
Save Le_max_left_zed;

(* end of new axiomatisation *)

Goal max_resp_times_zed : {x,y,a:int.1}(Le_zed zero_zed a) -> eq (max_zed (times_zed a x) (times_zed a y)) (times_zed a (max_zed x y));
intros;
Refine Le_antisym_zed;
Refine decide_int x y;
intros;
Refine Le_trans_zed;
Refine +2 max_Le_right_zed;
Refine Le_resp_times_zed;
Refine max_is_least_zed;
Refine H1;
Refine eq_imp_Le_zed;
Refine eq_refl_ax;
Refine H;
intros;
Refine Le_trans_zed;
Refine +2 max_Le_left_zed;
Refine Le_resp_times_zed;
Refine max_is_least_zed;
Refine eq_imp_Le_zed;
Refine eq_refl_ax;
Refine Lt_imp_Le;
Refine H1;
Refine H;
Refine max_is_least_zed;
Refine Le_resp_times_zed;
Refine max_Le_left_zed;
Refine H;
Refine Le_resp_times_zed;
Refine max_Le_right_zed;
Refine H;
Save max_resp_times_zed;

Goal min_resp_times_zed : {x,y,a:int.1}(Le_zed zero_zed a) ->(eq (min_zed (times_zed a x) (times_zed a y)) (times_zed a (min_zed x y)));
intros;
Refine Le_antisym_zed;
Refine min_is_greatest_zed;
Refine Le_resp_times_zed;
Refine min_Le_left_zed;
Refine H;
Refine Le_resp_times_zed;
Refine min_Le_right_zed;
Refine H;
Refine decide_int x y;
intros;
Refine Le_trans_zed;
Refine +1 min_Le_left_zed;
Refine Le_resp_times_zed;
Refine min_is_greatest_zed;
Refine eq_imp_Le_zed;
Refine eq_refl_ax;
Refine H1;
Refine H;
intros;
Refine Le_trans_zed;
Refine +1 min_Le_right_zed;
Refine Le_resp_times_zed;
Refine min_is_greatest_zed;
Refine Lt_imp_Le;
Refine H1;
Refine eq_imp_Le_zed;
Refine eq_refl_ax;
Refine H;
Save min_resp_times_zed;

Goal max_sym_zed : {x,y:int.1}(eq (max_zed x y) (max_zed y x));
intros;
Expand eq int eq_on_ints Eq_zed max_zed;
Qrepl plus_commutes x.2 y.2;
Qrepl plus_commutes x.1 y.2;
Qrepl plus_commutes x.2 y.1;
Qrepl max_sym|(plus y.2 x.1)|(plus y.1 x.2);
Refine Eq_refl;
Save max_sym_zed;

Goal min_sym_zed : {x,y:int.1}(eq (min_zed x y) (min_zed y x));
intros;
Expand eq int eq_on_ints Eq_zed min_zed;
Qrepl plus_commutes x.2 y.2;
Qrepl plus_commutes x.1 y.2;
Qrepl plus_commutes x.2 y.1;
Qrepl min_sym|(plus y.2 x.1)|(plus y.1 x.2);
Refine Eq_refl;
Save min_sym_zed;

Goal min_zed_idemp : {a|zed}Eq_zed (min_zed a a) a;
Intros; Expand min_zed Eq_zed;
Qrepl plus_commutes a.2 a.1;
Qrepl min_idemp (plus a.1 a.2);
Refine plus_assoc;
Save; 
