Module lib_nat_times_thms Import lib_nat_plus_thms;

(* Contents
   --------
   o Several theorems about multiplication.

   Changes
   -------

   Thomas Schreiber <tms@dcs.ed.ac.uk>
   17 Jan 1996
   added times_two
*)


Goal times_plus_dist_r : {i,j,k|nat}Eq (times (plus i j) k) (plus (times i k) (times j k));
    intros;
    Refine nat_ind [i:nat]{j,k|nat}
                Eq (times (plus i j) k) (plus (times i k) (times j k));
    intros;Refine Eq_refl;
    intros;
    Qrepl (plus_assoc k1 (times n k1) (times j1 k1));
    Refine Eq_resp (plus ?);
    Try Immed;
Save times_plus_dist_r;


Goal times_plus_dist_l : {i,j,k|nat}Eq (times i (plus j k)) (plus (times i j) (times i k));
    intros;
    Refine nat_ind [i:nat]
          {j,k|nat}Eq (times i (plus j k)) (plus (times i j) (times i k));
    intros;Refine Eq_refl;
    intros;Refine Eq_trans;Refine +2 middle_four_plus;
    Refine Eq_resp (plus (plus ? ?));Try Immed;
Save times_plus_dist_l;


Goal times_assoc : {i,j,k|nat}Eq (times (times i j) k) (times i (times j k));
    intros;
    Refine nat_ind [i:nat]
          {j,k|nat}Eq (times (times i j) k) (times i (times j k));
    intros;Refine Eq_refl;
    intros;Refine Eq_trans;
    Refine +1 times_plus_dist_r;Refine Eq_resp (plus (times ? ?));Try Immed;
Save times_assoc;


Goal times_zero : {n|nat}Eq zero (times n zero);
    intros;Refine nat_ind [n:nat]Eq zero (times n zero);
    Refine Eq_refl;
    intros;Try Immed;
Save times_zero;


Goal times_one : {n|nat}Eq n (times one n);
    intros;Refine nat_ind [n:nat]Eq n (times one n);
    Refine Eq_refl;intros;Refine Eq_resp suc;Try Immed;
Save times_one;


Goal zero_times_lemma : {m,n|nat}{eq0:Eq zero (times m n)}or(Eq zero m) (Eq zero n);
    intros;Refine nat_ind [m:nat]{n|nat}
        {eq0:Eq zero (times m n)}or(Eq zero m) (Eq zero n);Try Immed;
    intros;Refine inl;Refine Eq_refl;Try Immed;
    intros;Refine inr;Refine Eq_sym;
    Refine fst(plus_strict|?|? ?);Refine +1 Eq_sym eq01;
Save zero_times_lemma;


Goal one_times_lemma : {m,n|nat}{eq1:Eq one (times m n)}and (Eq one m) (Eq one n);
    intros; Refine nat_ind [m:nat]{n|nat}
         {eq1:Eq one (times m n)}and(Eq one m)(Eq one n);Try Immed;
    intros;Refine zero_not_one;Refine Eq_sym;Try Immed;
    intros;Refine one_plus_lemma eq11;
    intros eqs;Refine zero_times_lemma (snd eqs);
    intros eq2;Refine pair;Refine Eq_resp suc eq2;Refine fst eqs;
    intros eq2;Refine zero_not_one;
    Qrepl (fst eqs); Try Immed;
    intros eqs;Refine zero_not_one;
    Qrepl (fst eqs); 
    Refine Eq_sym  (snd (H (snd eqs)));
Save one_times_lemma;


Goal times_commutes : {m,n|nat}Eq (times m n) (times n m);
    intros;Refine nat_ind [n:nat]{m|nat}Eq (times m n) (times n m);Try Immed;
     intros;Refine nat_ind [m:nat]Eq (times m zero) zero;
            Refine Eq_refl;
            intros;Try Immed;
     intros;Refine nat_ind [m:nat]Eq (times m (suc ?)) (times (suc ?) m);
            Refine H|zero;
            intros;
    Equiv Eq (plus (suc ?) (times ? (suc ?))) 
             (plus (suc ?) (times ?  (suc ?)));
    Qrepl H1;Refine Eq_resp suc;
    Equiv Eq (plus ? (times (suc ?) ?)) (plus ? (times ? (suc ?)));
    Qrepl (Eq_sym (H|(suc n2)));
    Equiv Eq (plus ? (plus ?(times ? ?))) (plus ? (plus ? (times ? ?)));
    Qrepl (H|n2);
    Refine middle_four_plus|zero;
Save times_commutes;


Goal times_cancel_right : {a,x,y:nat}(Eq (times x (suc a)) (times y (suc a))) -> (Eq x y);
    intros a x y;
    Refine nat_diagonal_ind [x,y:nat]
               (Eq (times x (suc a)) (times y (suc a)))->Eq x y;
    intros;
    Refine zero_times_lemma;
    Refine m; Refine suc a;
    Refine H;
    Intros H1; Refine H1;
    intros;
    Refine zero_not_suc;
    Refine +1 H1;
    intros;
    Refine zero_times_lemma;
    Refine suc n; Refine suc a;
    Refine Eq_sym H;
    intros;
    Refine zero_not_suc;
    Refine +1 H1;
    intros;
    Refine zero_not_suc;
    Refine +1 H1;
    intros;
    Refine Eq_resp suc;
    Refine H;
    Refine cancel_plus (suc a);
    Refine H1;
Save times_cancel_right;

Goal times_two : {n:nat}(Eq (times two n) (plus n n));
intros; Equiv Eq (plus n (times ??)) ?;
Qrepl Eq_sym (times_one|n);
Refine Eq_refl;
Save;
















