Module lib_AS_eq Import lib_eq;

(* This file gives the extra elimination rule Eq_elim' 
   below which is used to derive the theorem Eq_unique.
   This rule is due to Altenkirch/Streicher. 
*)

[A|SET];

$[Eq_elim' : {C:{a|A}(Eq a a)->TYPE}
              ({a:A}C (Eq_refl a))
              -> {a|A}{p:Eq a a}C p];

Goal Eq_unique : {a,b:A}{p,q:Eq a b}Eq p q;
Intros a b p;
Equiv ([a,b|A][p:Eq a b]{q:Eq a b}Eq p q) p;
Refine Eq_elim;
Intros x q;
Equiv ([x|A][q:Eq x x]Eq (Eq_refl x) q) q;
Refine Eq_elim';
Intros a;
Refine Eq_refl;
Save Eq_unique;

Discharge A;


