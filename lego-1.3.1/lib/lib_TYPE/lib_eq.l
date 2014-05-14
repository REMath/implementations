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

$[Eq : {t|Type}t->t->Prop];

$[Eqr : {t|Type}{x:t}Eq x x];

$[Eq_elim : {t|Type}{P:{x,y:t}(Eq x y)->Type}({x:t}P x x (Eqr x))->
		{x,y:t}{p:Eq x y}P x y p];

[[t:Type]
 [P:{x,y:t}(Eq x y)->Type]
 [h:{x:t}P x x (Eqr x)]
 [x:t]
    Eq_elim P h x x (Eqr x) ==> h x];


Goal Eq_refl : {t|Type}refl (Eq|t);
	intros;
	Refine Eqr;
SaveUnfrozen Eq_refl;		(* otherwise Eq_unique can't be proven *)

Goal Eq_subst : {t|Type}{m,n|t}(Eq m n)->{P:t->Type}(P m)->P n;
        Intros ___;
        Refine Eq_elim|t ([x,y:t][_:Eq x y]{P:t->Type}(P x)->P y);
        Intros ___;
        Immed;
Save Eq_subst;

(* Make Theorems as powerful as possible *)
[trivType : Type = {T|Type}T->T];
[emptyType : Type = {T|Type}T];
Configure Theorems trivType emptyType Eq_subst;
