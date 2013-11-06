(* Time-stamp: <27 Jan 97 tms /home/lego/library/reorg/libs/lib_ML/lib_ML_nat.l> *)

Module lib_ML_nat Import lib_empty lib_unit lib_nat;

[C|Type];

Goal nat_diagonal : {f,g:nat->nat->C}{a,b:nat}C;
(*  nat_diagonal f _ a b = f a b where a and b stem from the same constructor *)
(* |nat_diagonal _ g a b = g a b *)
intros;
Refine nat_double_elim [a,b:nat]C;
[f' = f a b][g' = g a b];
intros; Refine f';
intros; Refine g';
intros; Refine g';
intros; Refine f'; 
Refine a; Refine b;
SaveUnfrozen;

[nat_diagonal_const [f,g:C] = nat_diagonal ([_,_:nat]f) ([_,_:nat]g)];

Discharge C;

[nat_filter = nat_diagonal_const|Type unit empty];

$Goal f : nat->Type;
Refine nat_elim [_:nat]Type;
Refine unit;
intros; Refine injective suc;
SaveUnfrozen;

$Goal g : nat->Type;
Refine nat_elim [n:nat]Type;
        Refine {n:nat}(Eq zero (suc n))->empty;
intros; Refine {n:nat}(Eq (suc n) zero)->empty;
SaveUnfrozen;

[nat_Thm = (nat_diagonal|Type) ([_:nat]f) ([_:nat]g)]; Discharge f;

$Goal get_filter : {m,n|nat}(Eq m n)->Type;
intros; Refine nat_filter m n; SaveUnfrozen;

Goal nat_thm : {u,v:nat}nat_Thm u v;
Refine nat_double_elim nat_Thm;
Refine void;

Intros; Equiv get_filter H1; Expand get_filter; Qrepl H1;
Refine void;

Intros; Equiv get_filter H1; Expand get_filter; Qrepl H1;
Refine void;

Intros; Equiv Eq (pred (suc x)) (pred (suc y));
Refine Eq_resp; Immed;
Save;

Discharge get_filter;
