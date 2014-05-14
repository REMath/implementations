Module lib_eq_inductive Import lib_logic;

(* Contents
   --------
   o Definition and rules for manipulating Christine Paulin-Mohring's
     inductive equality.

*)

Inductive [Eq:t->Prop] Parameters [t|Type][x:t] ElimOver Type
Constructors [Eqr : Eq x];
Discharge t;

Goal Eq_refl : {t|Type}refl (Eq|t);
	intros;
	Refine Eqr;
Save Eq_refl;

Goal Eq_subst : {t|Type}{m,n|t}(Eq m n)->{P:t->Type}(P m)->P n;
        intros;
        Refine Eq_elim|t m [y:t][p:Eq m y](P m)->P y;
        intros; Immed; Immed;
Save Eq_subst;




