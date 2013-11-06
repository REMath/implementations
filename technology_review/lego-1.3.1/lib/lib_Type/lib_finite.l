Module lib_finite Import lib_nat;

(** CHANGES

    7 March 1997 Thomas Schreiber <tms@dcs.ed.ac.uk>
      o added f_plus and f_plus_assoc
**)

Inductive
[fin:{n:nat}Type]
Constructors
[f_zero:{n:nat}(fin (suc n))]
[f_suc:{n|nat}{x:(fin n)}(fin (suc n))];

Goal f_plus : {n,m|nat}(fin n) -> fin (plus m n);
intros _;
Refine nat_elim [m:nat](fin n) -> fin (plus m n);
intros input;
Refine input;
intros input _ _;
Refine f_suc;
Refine x1_ih;
Immed;
Save;

Goal {n:nat}{m:fin (suc n)}{P:(fin (suc n))->Type}(P (f_zero n))->
	({m:fin n}P (f_suc m))->P m;
	intros _;
	Refine fin_elim (nat_elim ([x:nat](fin x)->Type) 
                 ([_:fin zero]trueProp)
		([x|nat][_:(fin x)->Type][n = suc x][m:fin n]
		{P:(fin n)->Type}(P (f_zero x))->
			({m:fin x}P (f_suc m))->P m));
	Intros; Immed;
	Intros; Refine H1;
Save fin_elim'_lemma;

[fin_elim' [n:nat][P:(fin (suc n))->Type]
	[p:P (f_zero n)][p':{m:fin n}P (f_suc m)][m:fin (suc n)] =
		fin_elim'_lemma n m P p p'];

[fin_rec [C|Type] = fin_elim [n:nat][_:fin n]C];
[fin_iter [C|Type][a:nat->C][f:nat->C->C] = fin_rec a [n:nat][_:fin n]f n];
[fin_ind [P:{n:nat}(fin n)->Prop] = fin_elim P];

[fin_rec' [n:nat][C|Type] = fin_elim' n [_:fin (suc n)]C];
[fin_ind' [n:nat][P:(fin (suc n))->Prop] = fin_elim' n P];

Goal peano2_fin : {n:nat}{x:fin n}not (Eq (f_suc x) (f_zero n));
	Intros ___;
	 Refine Eq_subst H (fin_rec' n absurd [_:fin n]trueProp);
	  Intros; Immed;
Save peano2_fin;

Goal peano3_fin : {n:nat}{x,y:fin n}(Eq (f_suc x) (f_suc y))->Eq x y;
	intros;
	 Refine Eq_subst H (fin_rec' n absurd ([x':fin n]Eq x x'));
	  Refine Eq_refl;
Save peano3_fin;

Goal inj_void : {n:nat}{x:fin (suc n)}
                     (not (Eq x (f_zero n)))->Ex [x':fin n]Eq x (f_suc x');
	intros n;
	 Refine fin_elim' n [x:fin (suc n)]
                  (not (Eq x (f_zero n)))->Ex ([x':fin n]Eq x (f_suc x'));
	  intros; Refine H; Refine Eq_refl;
	  intros; Refine ExIntro; Refine m; Refine Eq_refl;
Save inj_void;


Goal finite_is_zero_or_succ : {n:nat}{x:fin (suc n)}
      (or (Eq x (f_zero n)) (Ex [x':fin n]Eq x (f_suc x')));
intros n;
Refine fin_elim' n [x:fin (suc n)](or (Eq x (f_zero n)) 
                             (Ex [x':fin n]Eq x (f_suc x')));
intros;
Refine inl; Refine Eq_refl;
intros;
Refine inr;
Refine ExIntro;
Refine +1 Eq_refl;
Save finite_is_zero_or_succ;

Goal zero_set_is_empty : {x:fin zero}absurd;
intros;
Refine fin_elim ([n|nat][v:fin n](Eq n zero)->absurd);
intros;
Refine zero_not_suc;
Refine +1 Eq_sym H;
intros;
Refine zero_not_suc;
Refine +1 Eq_sym H;
Refine +1 x; Refine Eq_refl;
Save zero_set_is_empty;

Goal fin_zero_lemma : {n|nat}{x:fin n}((nat_elim ([x:nat](fin x)->Type) 
([x:fin zero]{P:(fin zero)->Type}P x) ([n:nat][_:(fin n)->Type]
[_:fin (suc n)]{t:Type}t->t)) n x);
Refine fin_elim (nat_elim ([x:nat](fin x)->Type) 
([x:fin zero]{P:(fin zero)->Type}P x) ([n:nat][_:(fin n)->Type]
[_:fin (suc n)]{t:Type}t->t));
Intros;
Immed;
Intros;
Immed;
Save fin_zero_lemma;

Goal fin_elim_zero : {P:(fin zero)->Type}{x:fin zero}P x;
Intros;
Refine fin_zero_lemma x;
Save fin_elim_zero;

Goal f_plus_assoc : 
  {n,o,m|nat}(fin (m .plus (n .plus o))) -> fin ((m .plus n) .plus o);
intros __;
Induction m;

  Refine Id;			(* base case *)

  (** step case **)
  intros __; 
  Refine fin_elim' ? [_:fin (plus (suc x1) (plus n o))]
    fin (plus (plus (suc x1) n) o);
    Refine f_zero;		(* base case *)

    (** step case **)
    intros; Refine f_suc; Refine x1_ih; Immed;
Save f_plus_assoc;

Goal fin_to_nat : {n|nat}{x:fin n}nat;
Refine fin_elim ([n|nat][x:fin n]nat);
Refine [n:nat]zero;
intros;
Refine suc x_ih;
Save fin_to_nat;

Goal fin_to_nat_resp_suc : {n|nat}{x:fin n}(Eq (suc (fin_to_nat x)) (fin_to_nat (f_suc x)));
Refine fin_ind [n|nat][x:fin n](Eq (suc (fin_to_nat x)) (fin_to_nat (f_suc x)));
intros;
Refine Eq_refl;
intros;
Refine Eq_resp;
Refine x_ih;
Save fin_to_nat_resp_suc;
