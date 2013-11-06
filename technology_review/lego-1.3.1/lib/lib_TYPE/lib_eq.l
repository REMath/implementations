Module lib_eq Import lib_logic;

(* Contents
   --------
   o Definition and rules for manipulating Martin-Lof's inductive equality.

   Note
   ----
   o We cannot use Lego's inductive type mechanism for this definition 
     because the type of the constructor Eqr violates the conditions laid
     down in Luo's schema for inductive types.
*)

$[Eq : {t|SET}t->t->Prop];

$[Eqr : {t|SET}{x:t}Eq x x];

$[Eq_elim : {t|SET}{P:{x,y:t}(Eq x y)->TYPE}({x:t}P x x (Eqr x))->
		{x,y:t}{p:Eq x y}P x y p];

[[t:SET]
 [P:{x,y:t}(Eq x y)->TYPE]
 [h:{x:t}P x x (Eqr x)]
 [x:t]
    Eq_elim P h x x (Eqr x) ==> h x];


Goal Eq_refl : {t|SET}refl (Eq|t);
	intros;
	Refine Eqr;
SaveUnfrozen Eq_refl;		(* otherwise Eq_unique can't be proven *)

Goal Eq_subst : {t|SET}{m,n|t}(Eq m n)->{P:t->TYPE_minus1}(P m)->P n;
        Intros ___;
        Refine Eq_elim|t ([x,y:t][_:Eq x y]{P:t->TYPE_minus1}(P x)->P y);
        Intros ___;
        Immed;
Save Eq_subst;

(* Make Theorems as powerful as possible *)
[trivType : TYPE_minus1 = {T|TYPE_minus2}T->T];
[emptyType : TYPE_minus1 = {T|TYPE_minus2}T];
Configure Theorems trivType emptyType Eq_subst;
