Module lib_int_basics Import lib_int_nat_lemmas 
			     lib_nat_minus_thms
                             lib_sets_ccmj;
(* zed.l *)

(* the integers as a per over nat x nat *)
[zed = nat#nat];
(* some random facts about the natural numbers which we need *)


[Eq_zed = [mm,nn:zed]
        Eq (plus mm.1 nn.2) (plus nn.1 mm.2):(zed -> zed -> Prop)];

Goal Eq_refl_zed : refl Eq_zed;
Intros _;
Refine Eq_refl;
Save Eq_refl_zed;

Goal Eq_sym_zed : sym Eq_zed;
Intros mm nn eq;Refine Eq_sym;Try Immed;
Save Eq_sym_zed;

Goal Eq_trans_zed : trans Eq_zed;
Intros mm nn pp;[m1 = mm.1][m2 = mm.2][n1 = nn.1][n2 = nn.2][p1 = pp.1]
[p2 = pp.2];
Intros eql eqr;
Refine cancel_plus n1;
Refine Eq_trans;
Refine +1 middle_four_plus|zero|?|?|? ;Qrepl eqr;
Refine Eq_subst (middle_four_plus|zero|?|?|?);
Refine Eq_sym;
Refine Eq_subst (middle_four_plus|?|?|?|?);
Qrepl eql;
Refine Eq_refl;
Save Eq_trans_zed;


(* now earlier on Include math;  *)
Goal int : set;
Intros#;
Refine zed;
Intros#;
Refine Eq_zed;
Refine pair3;
Refine Eq_refl_zed;
Refine Eq_sym_zed;
Refine Eq_trans_zed;
SaveUnfrozen int;


(* some operations !!! *)
[zero_zed  = (zero,zero):int.1];
[one_zed = (one,zero):int.1];
[two_zed = (two,zero):int.1];
[three_zed = (three,zero):int.1];
[four_zed = (four,zero):int.1];
[minus_one_zed = (zero,one):int.1];
[plus_zed [mm,nn:int.1] = 
                     (plus mm.1 nn.1,plus mm.2 nn.2):int.1];

[times_zed [mm,nn:int.1] = 
       (plus (times mm.1 nn.1) (times mm.2 nn.2), plus (times mm.1 nn.2) (times mm.2 nn.1))
       :int.1];

minus_zed [a,b:int.1] == (plus a.1 b.2, plus a.2 b.1):int.1;

neg_zed [a:int.1] == (a.2,a.1):int.1;













