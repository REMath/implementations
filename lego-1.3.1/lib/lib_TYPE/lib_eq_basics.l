Module lib_eq_basics Import lib_eq;

(* Contents
   --------
   o Lemmata for arbitrary substitutive (equality) relation 

   Credit
   ------
   Thomas Schreiber
*)

[injective [S,T|Type][f:S->T] = {x,y:S}(Eq (f x) (f y))->Eq x y];

Goal Eq_sym : {t|Type}sym (Eq|t);
	Expand sym; intros;
	Refine Eq_subst H ([x:t]Eq x t1) (Eq_refl t1);
Save Eq_sym;


Goal Eq_trans : {t|Type}trans (Eq|t);
	Expand trans; intros;
	Refine Eq_subst H1 ([x:t]Eq t1 x) H;
Save;

Goal Eq_resp : {A,B|Type}{f:A->B}respect f Eq;
	Expand respect; intros;
	Refine Eq_subst H ([x:A]Eq (f t) (f x)) (Eq_refl (f t));
Save;

Configure Equality Eq Eq_refl Eq_subst;

Goal Eq_resp2 : {A,B,C|Type}{r:A->B->C}respect2 r Eq;
        Expand respect2; intros;
        Qrepl H; Qrepl H1;
        Refine Eq_refl;
Save Eq_resp2;

