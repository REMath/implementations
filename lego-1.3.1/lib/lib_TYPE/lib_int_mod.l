Module lib_int_mod Import lib_int_basics_thms;

[Mod [m,x,r:int.1] = Ex [k:int.1]eq (plus_zed r (times_zed k m)) x];

Goal plus_resp_mod : {m,x1,x2,r1,r2|int.1}{mod1:Mod m x1 r1}{mod2:Mod m x2 r2}
                      Mod m (plus_zed x1 x2) (plus_zed r1 r2);
intros;
Refine mod1;intros k1 eq1;
Refine mod2;intros k2 eq2;
Refine ExIntro;Refine plus_zed k1 k2;
Refine Eq_trans_zed;Refine +1 plus_resp_eq;Refine +3 times_plus_dist_r_zed;
Refine +2 Eq_trans_zed;Refine +3 middle_four_plus_zed;Refine +3 plus_resp_eq;
Refine Eq_refl_zed;Try Immed;
Save plus_resp_mod;

(* likewise for multiplication *)
Goal times_resp_Mod : {m,x1,x2,r1,r2|int.1}(Mod m x1 r1)->(Mod m x2 r2)->
      Mod m (times_zed x1 x2) (times_zed r1 r2);
intros;
Refine H;intros k1 hyp1;
Refine H1;intros k2 hyp2;
Refine ExIn;
Next +1;
Refine Eq_trans_zed;Refine +2 times_resp_eq ? ? ? ? hyp1 hyp2;

Refine Eq_trans_zed;Refine +2 Eq_sym_zed;Refine +2 times_plus_dist_l_zed;

Refine Eq_trans_zed;Refine +2 plus_resp_eq;
Refine +3 Eq_sym_zed;Refine +3 times_plus_dist_r_zed;
Refine +2 Eq_sym_zed;Refine +2 times_plus_dist_r_zed;

Refine Eq_trans_zed;Refine +2 Eq_sym_zed;Refine +2 plus_assoc_zed;
Refine plus_resp_eq;Refine Eq_refl_zed;

Refine Eq_trans_zed;Refine +2 plus_resp_eq;
Refine +3 Eq_trans_zed;Refine +5 Eq_sym_zed;Refine +5 times_assoc_zed;

Refine +3 Eq_trans_zed;Refine +5 times_resp_eq;Refine +6 Eq_refl_zed;
Refine +5 Eq_subst (times_commutes_zed|?|?);Refine +5 Eq_refl_zed;Refine +3 times_assoc_zed;
Refine times_plus_dist_r_zed;

Next +1;Refine Eq_trans_zed;
Refine +1 times_plus_dist_r_zed;
Refine +2 plus_resp_eq;
Refine +2 times_assoc_zed;Refine +1 times_assoc_zed;
Save times_resp_Mod;

