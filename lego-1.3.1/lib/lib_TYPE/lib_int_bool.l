Module lib_int_bool Import lib_int_Prop_rels lib_nat_rels;

(* Boolean stuff on integers *)

Goal int_eq_zero : int.1 -> bool;
Intros x; 
Refine nat_eq x.1 x.2;
SaveUnfrozen int_eq_zero;

Goal int_Le_bool : int.1 -> int.1 -> bool;
Intros x y;
Refine le (plus x.1 y.2) (plus y.1 x.2);
SaveUnfrozen int_Le_bool;

Goal int_eq_bool : int.1 -> int.1 -> bool;
Intros x y;
Refine nat_eq (plus x.1 y.2) (plus y.1 x.2);
SaveUnfrozen int_eq_bool;

Goal int_Lt_bool : int.1 -> int.1 -> bool;
Intros x y;
Refine lt (plus x.1 y.2) (plus y.1 x.2);
SaveUnfrozen int_Lt_bool;

Goal bool_pos : int.1 -> bool;
Intros x;
Refine le x.2 x.1;
SaveUnfrozen bool_pos;

Goal bool_pos_true_imp_pos : {x:int.1}(Eq (bool_pos x) true) -> (Le_zed zero_zed x);
intros;
Refine le_true_imp_Le;
Refine H;
Save bool_pos_true_imp_pos;

Goal bool_pos_false_imp_pos : {x:int.1}(Eq (bool_pos x) false) -> (Lt_zed x zero_zed);
intros;
Refine le_false_imp_Lt;
Qrepl plus_zero x.1;
Qrepl plus_zero x.2;
Refine H;
Save bool_pos_false_imp_pos;


Goal pos_imp_bool_pos_true : {x:int.1}(Le_zed zero_zed x) -> (Eq (bool_pos x) true);
intros;
Refine Le_imp_le_true;
Refine H;
Save pos_imp_bool_pos_true;

Goal pos_imp_bool_pos_false : {x:int.1}(Lt_zed x zero_zed) -> (Eq (bool_pos x) false);
intros;
Refine Lt_imp_le_false;
Qrepl Eq_sym (plus_zero x.1);
Qrepl Eq_sym (plus_zero x.2);
Refine H;
Save pos_imp_bool_pos_false;





