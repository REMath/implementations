Module lib_nat_div Import lib_nat_rels lib_bool_thms;

Goal half : {n:nat}nat;
Refine nat_elim [n:nat]nat;
  Refine zero;			(* half 0 *)
  intros n half_n;		(* ?half (suc n) *)
  Refine if (even n) half_n (suc half_n) ;
Save;
	    
Goal even_pred : 
  {n|nat}{b|bool}(Eq (even (suc n)) (inv b)) -> Eq (even n) b;
Refine nat_ind [n:nat]{b|bool}(Eq (even (suc n)) (inv b)) -> Eq (even n) b;
  Refine bool_elim [b:bool](Eq (even (suc zero)) (inv b))->Eq (even zero) b;
    intros; Refine Eq_refl;
    Refine Eq_sym;

  (** step case **)
  intros __;
  Refine bool_elim [b:bool](Eq (even (suc (suc n))) (inv b))->
                           Eq (even (suc n)) b;
    intros;
    Refine snd (inv_character' ??);
    Refine H;
    Refine snd (inv_character' ??);
    Refine Eq_trans; Try Immed;
    Refine Eq_sym; Refine inv_idemp;    
    
    intros;
    Refine snd (inv_character' ??);
    Refine H;
    Refine snd (inv_character' ??);
    Refine Eq_trans; Try Immed;
    Refine Eq_sym; Refine inv_idemp;
Save;


Goal half_even : 
  {n:nat}and ((is_true (even n)) -> Eq (times two (half n)) n)
             ((is_false (even n)) -> Eq (suc (times two (half n))) n);

Refine nat_ind [n:nat]and ((is_true (even n)) -> Eq (times two (half n)) n)
             ((is_false (even n)) -> Eq (suc (times two (half n))) n);

  (** base case **)
  Refine pair;
    intros; Refine Eq_refl;
    intros; Refine true_not_false; Try Immed;

  (** step case **)
  intros; Refine H; intros;
  Refine bool_elim [b:bool](Eq (even n) b)->
        and ((is_true (inv b))->Eq (times two (half (suc n))) (suc n))
            ((is_false (inv b))->
             Eq (suc (times two (half (suc n)))) (suc n));
  Refine -0 Eq_refl;

    (** n even **)
    intros n_even;
    Refine pair;
      intros; Refine true_not_false; Refine Eq_sym; Try Immed;
      intros; Refine Eq_resp suc;
      Expand half; Qrepl n_even;
      Refine H1; Try Immed;

    (** n odd **)
    intros n_odd;
    Refine pair;

      intros; Expand half; Qrepl n_odd;
      Refine Eq_resp suc;
      Qrepl plus_zero (suc (half n));
      Refine Eq_trans; Refine -1 plus_commutes;
      Refine Eq_trans; Refine -0 H2; Try Immed;
      Refine Eq_resp; Refine Eq_sym;
      Refine plus_zero;

      intros; Refine true_not_false; Try Immed;
Save;


