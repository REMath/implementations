Module lib_nat_Lt Import lib_nat_minus_thms;

(* Contents
   --------
   o A Prop-valued definition of the "less than" ordering on natural numbers.
   o Theorems about this ordering, including the principles of complete
     induction and well-founded induction.  
*) 

[Lt = [n,m:nat] Ex[k:nat] Eq (plus n (suc k)) m : nat->nat->Prop];

Goal zero_Lt_suc_n : {n:nat}Lt zero (suc n);
intros; Refine ExIntro; Refine n; Refine Eq_refl;
Save zero_Lt_suc_n;                                                     


Goal n_Lt_suc_n : {n:nat}Lt n (suc n);
Intros n; Refine ExIntro; Refine zero;
Refine (Eq_subst (plus_commutes ? ?)) [t:nat]Eq t ?; Refine Eq_refl;
Save n_Lt_suc_n;                                                       


Goal Lt_trans : {l,m,n|nat}(Lt l m)->(Lt m n)->(Lt l n);
Intros l m n Ltlm Ltmn;
Refine Ltlm; Intros o EqlSucom; Refine Ltmn; Intros p EqmSucpn;
Refine ExIntro; Refine suc (plus o p);
Equiv Eq (plus l (plus (suc (suc o)) p)) n;
Refine (Eq_subst (plus_assoc ? ? ?)) [t:nat]Eq t n;
Refine (Eq_subst (Eq_sym (plus_suc ? ?))) [t:nat]Eq (plus t p) n;
Refine (Eq_subst (Eq_sym EqlSucom)) [t:nat]Eq (plus (suc t) p) n;
Equiv Eq (suc (plus m p)) n;
Refine (Eq_subst (plus_suc m p)) [t:nat]Eq t n;
Try Immed;
Save Lt_trans;                                                           


Goal not_n_Lt_zero : {n:nat}not (Lt n zero);
Intros n LtnZero; Refine LtnZero; Intros t h;
Refine zero_not_suc (plus n t);
Refine (Eq_subst (plus_suc ? ?)) [u:nat]Eq zero u;
Refine Eq_sym h;
Save not_n_Lt_zero;      

                  
Goal not_refl_Lt : {x:nat}(not (Lt x x));
Intros x H; Refine H; intros;
Refine plus_suc_lemma;
Refine +2 H1;
Save not_refl_Lt;
                                

Goal Lt_not_Eq : 
     {x,y:nat}(Lt x y)->(not (Eq x y));
intros; Refine H; intros; Qrepl Eq_sym H1; 
Intros _; Refine plus_suc_lemma x t; Refine Eq_sym H2;
Save;

Goal Lt_zero :
  {n:nat}(not (Eq n zero)) -> Lt zero n;

  Refine nat_elim [n:nat](not (Eq n zero)) -> Lt zero n;
    intros H; Refine H; Refine Eq_refl;	(* base case *)
    intros; Refine zero_Lt_suc_n; 
Save;


Goal Lt_resp_suc : {m,n:nat}(Lt m n)  -> Lt (suc m) (suc n);
Intros m n; 
Intros Ltmn; Refine Ltmn; Intros t h; Refine ExIntro; Refine t;
Refine Eq_resp_suc h;
Save Lt_resp_suc;                                                         


Goal Lt_resp_pred : {x,y:nat}(Lt (suc x) (suc y)) -> (Lt x y);
intros;
Refine H; intros;
Refine ExIntro;
Refine t;
Refine suc_injective;
Qrepl H1;
Refine Eq_refl;
Save Lt_resp_pred;

Goal Lt_pred : {a,b|nat}(Lt a b) -> Lt (pred b) b;
Induction b;
intros; Refine not_n_Lt_zero; Immed;
intros; Refine n_Lt_suc_n;
Save Lt_pred;

Goal Lt_suc_pred : {a,b|nat}(Lt (suc a) b) -> Lt a (pred b);
Induction b;
intros; Refine not_n_Lt_zero; Immed;
intros; Refine Lt_resp_pred; Immed; 
Save Lt_suc_pred;

Goal Lt_not_zero : {a,b|nat}(Lt a b) -> not (Eq b zero);
Expand not;
Induction b Then Qnify;
  Refine not_n_Lt_zero; Immed;
Save Lt_not_zero;

Goal Lt_pred_suc : {a,b|nat}(Lt a (pred b)) -> Eq b (suc (pred b));
Induction b;
intros; Refine not_n_Lt_zero; Immed;
intros; Refine Eq_refl;
Save Lt_pred_suc;

Goal Lt_pred_suc' : {a,b|nat}(Lt (pred a) b) -> Lt a (suc b);
Induction a;
intros; Refine zero_Lt_suc_n;
intros; Refine Lt_resp_suc; Immed;
Save Lt_pred_suc'; 

Goal Lt_pred_suc'' : {a,b|nat}(Lt a (pred b)) -> Lt (suc a) b;
intros; Qrepl Lt_pred_suc H; Refine Lt_resp_suc; Immed;
Save Lt_pred_suc'';


Goal n_Lt_suc_m_character : {n,m|nat}(Lt n (suc m))->or (Lt n m) (Eq n m);
intros; Refine H; 
Refine nat_ind [t:nat](Eq (plus n (suc t)) (suc m))->or (Lt n m) (Eq n m);
intros; Refine inr; Refine suc_injective;
   Qrepl Eq_sym H1; Qrepl plus_suc n zero; Qrepl plus_zero n; Refine Eq_refl;
intros; Refine inl; Refine ExIntro; Refine n1; Refine suc_injective;
   Qrepl Eq_sym H2; Refine Eq_sym; Refine plus_suc;
Save n_Lt_suc_m_character;                                                  


(* Lt and plus *)
Goal plus_resp_Lt_l : {l,m|nat}(Lt l m)->{n:nat}Lt (plus l n) (plus m n);
intros l m Ltlm;
Refine nat_ind [n:nat]Lt (plus l n) (plus m n);
Qrepl plus_zero l; Qrepl plus_zero m; Try Immed;
intros x Ltlxmx;
Qrepl plus_suc l x; Qrepl plus_suc m x;
Refine Lt_resp_suc (plus l x) (plus m x); Try Immed;
Save plus_resp_Lt_l;                                                    


Goal Lt_resp_plus : {x,y,z:nat}(Lt x y) -> (Lt (plus z x) (plus z y));
Intros x y z;
Refine nat_ind [z:nat](Lt x y)->Lt (plus z x) (plus z y);
intros; Refine H;
intros;
Refine Lt_resp_suc ? ?;
Refine H;
Refine H1;
Save Lt_resp_plus;


Goal Lt_resp_plus_both : {x,y,a,b:nat}(Lt x y) -> 
(Lt a b) -> (Lt (plus x a) (plus y b));
Intros x y a b h1 h2;
Refine Lt_trans;
Refine +1 Lt_resp_plus;
Refine +1 h2;
Qrepl plus_commutes x b;
Qrepl plus_commutes y b;
Refine Lt_resp_plus; Refine h1;
Save Lt_resp_plus_both;

Goal Lt_resp_plus_right : {a,x,y|nat}(Lt x y) -> Lt x (plus a y);
Refine nat_elim [a:nat]{x,y|nat}(Lt x y) -> Lt x (plus a y);
intros; Try Immed;
intros; Refine Lt_trans;
Refine +1 x1_ih;
Refine +2 n_Lt_suc_n; Try Immed;
Save;

Goal Lt_resp_times : {x,y,a:nat}(Lt x y) -> 
  (Lt (times (suc a) x) (times (suc a) y));
Intros x y a;
Refine nat_ind [a:nat]((Lt x y)->Lt (times (suc a) x) (times (suc a) y));
Intros H;Refine H; intros;
Refine ExIntro;
Refine t;
Qrepl (plus_zero y);
Qrepl (plus_zero x);
Refine H1;
intros;
Refine Lt_resp_plus_both;
Refine H1;
Refine H;
Refine H1;
Save Lt_resp_times;

Goal Lt_resp_sub : {x,y,z:nat}(Lt (plus z x) (plus z y)) -> (Lt x y);
Intros x y z;
Refine nat_ind [z:nat](Lt (plus z x) (plus z y))->Lt x y;
intros; Refine H;
intros;
Refine H;
Refine Lt_resp_pred;
Refine H1;
Save Lt_resp_sub;


Goal Lt_times_cancel : {x,y,a:nat}(Lt (times x (suc a)) (times y (suc a)))
   -> (Lt x y);
Intros x y a;
Refine nat_diagonal_ind
         [x,y:nat]((Lt (times x (suc a)) (times y (suc a)))->Lt x y);
intros m;
Refine nat_ind [m:nat](
(Lt (times zero (suc a)) (times m (suc a)))->Lt zero m);
intros;
Refine not_n_Lt_zero;
Refine +1 H;
intros;
Refine zero_Lt_suc_n;
intros;
Refine not_n_Lt_zero;
Refine +1 H;
intros;
Refine Lt_resp_suc ? ?;
Refine H;
Refine Lt_resp_sub;
Refine +1 H1;
Save Lt_times_cancel;


Goal ze_Lt_imp_Eq_suc : {m:nat}(Lt zero m) -> (Ex [n:nat](Eq m (suc n)));
intros m;
Refine nat_ind [m:nat]((Lt zero m)->Ex ([n:nat]Eq m (suc n)));
intros;
Refine not_n_Lt_zero;
Refine +1 H;
intros;
Refine ExIntro;
Refine +1 Eq_refl;
Save ze_Lt_imp_Eq_suc;


Goal exists_suc : {P:nat->Prop}{n:nat}iff (Ex[t:nat](Lt t (suc n))/\(P t))
((Ex[t:nat](Lt t n)/\(P t))\/(P n));
intros;
Refine pair;
intros;
Refine H;
intros;
Refine n_Lt_suc_m_character (fst H1);
intros;
Refine inl;
Refine ExIntro;
Refine +1 pair;
Refine +1 H2;
Refine snd H1;
intros;
Refine inr;
Qrepl (Eq_sym H2);
Refine snd H1;
intros;
Refine H;
intros;
Refine H1;
intros;
Refine ExIntro t;
Refine pair ? (snd H2);
Refine Lt_trans (fst H2); 
Refine n_Lt_suc_n;
intros;
Refine ExIntro n;
Refine pair ? H1;
Refine n_Lt_suc_n;
Save exists_suc;

Goal complete_induction : {P:nat->Prop}
     {wf_ih:{n:nat}({x:nat}(Lt x n)->(P x))->P n}
     {m:nat}P m;
intros; Refine wf_ih;
Refine nat_ind [m:nat]{x:nat}(Lt x m)->P x;
intros; Refine not_n_Lt_zero; Try Immed;
intros; Refine n_Lt_suc_m_character H1;
intros; Refine H x H2;
intros; Refine wf_ih; Qrepl H2; Refine H;
Save complete_induction;

Goal well_founded_induction : {t|Type}{f:t->nat}{P:t->Prop}
 {ih:{x:t}({y:t}(Lt (f y) (f x)) -> (P y)) -> P x}
 {z:t}P z;
 intros;
 Refine complete_induction [n:nat]{y:t}(Eq n (f y))->P y;
 Refine +2 Eq_refl;
 intros;
 Refine ih; intros;
 Refine H;
Refine f y1;
Qrepl H1;
Refine H2; Refine Eq_refl;
Save well_founded_induction;

(* Lexicographic induction...essentially nested complete induction *)


Goal nested_complete_induction : {P:nat->nat->Prop}
     {wf_ih:{n,m:nat}
        {ih:{x,y:nat}(or (Lt x n) (and (Eq x n) (Lt y m)))->P x y}
           P n m}
     {n,m:nat}P n m;
intros;
Refine complete_induction [n:nat]{m:nat}P n m;
intros;
Refine complete_induction [m1:nat](P n1 m1);
intros; Refine wf_ih;
intros; Refine H2;
intros; Refine H; Try Immed;
intros; Qrepl fst H3;
Refine H1; Refine snd H3;
Save nested_complete_induction;
