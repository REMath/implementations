Module lib_nat_Lt_ML Import lib_ML lib_nat_Lt;

(* Contents
   --------
   o comple and well-founded elimination which is only provable using
     Martin Loef equality  *) 

Goal complete_elimination :{P:nat->TYPE}
     {wf_ih:{n:nat}({x:nat}(Lt x n)->(P x))->P n}
     {m:nat}P m;
intros; Refine wf_ih;
Refine nat_elim [m:nat]{x:nat}(Lt x m)->P x;
intros; Refine empty_elim [_:empty]P x;
Refine absurd_impl_empty;	(* we require ML equality here *)
Refine not_n_Lt_zero ? H;
intros;
Refine wf_ih; intros; Refine x1_ih;
Refine H; intros;
Refine Lt_resp_pred; Qrepl Eq_sym H2;
Qrepl plus_suc x t;
Refine Lt_resp_suc; 
Qrepl plus_commutes x t; Refine Lt_resp_plus_right;
Try Immed;
SaveUnfrozen;

Goal well_founded_elimination:
       {t|TYPE}{f:t->nat}{P:t->TYPE}
       {ih:{x:t}({y:t}(Lt (f y) (f x)) -> (P y)) -> P x}
       {z:t}P z;
 intros;
 Refine complete_elimination [n:nat]{y:t}(Eq n (f y))->P y;
 Refine +2 Eq_refl;
 intros;
 Refine ih; intros;
 Refine H;
 Refine f y1;
 Qrepl H1;
 Refine H2; 
 Refine Eq_refl;
 SaveUnfrozen;
