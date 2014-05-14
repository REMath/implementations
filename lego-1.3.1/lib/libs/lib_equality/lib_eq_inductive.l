Module lib_eq_inductive Import lib_logic;

(* Contents
   --------
   o Definition and rules for manipulating Christine Paulin-Mohring's
     inductive equality.

*)

Inductive [Eq:t->Prop] Parameters [t|SET][x:t] ElimOver TYPE
Constructors [Eqr : Eq x];
Discharge t;

Goal Eq_refl : {t|SET}refl (Eq|t);
	intros;
	Refine Eqr;
Save Eq_refl;

Goal Eq_subst : {t|SET}{m,n|t}(Eq m n)->{P:t->TYPE_minus1}(P m)->P n;
        intros;
        Refine Eq_elim|t m [y:t][p:Eq m y](P m)->P y;
        intros; Immed; Immed;
Save Eq_subst;




