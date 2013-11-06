Module lib_nat_iter Import lib_nat lib_bool_funs;


Goal nat_iter_suc : {t|Type}{z:t}{s:t->t}{n:nat}Eq (nat_iter z s (suc n)) (nat_iter (s z) s n);
intros;
Refine nat_ind[n:nat]Eq (nat_iter z s (suc n)) (nat_iter (s z) s n);
Refine Eq_refl;
intros _;
Refine Eq_resp s;
Save nat_iter_suc;


Goal while_cond1 : {f:nat->bool}[lll=nat_iter zero ([a:nat]if (f (suc a)) (suc a) a)]
(is_true (f zero))->{n:nat}(is_true (f (lll n)));
intros f lll fzero;
Refine nat_ind[n:nat]is_true (f (lll n));
Refine fzero;
Intros n ih;
Expand lll nat_iter nat_rec;
Refine true_or_false (f (suc (lll n)));
Intros Qtt;
Qrepl Qtt;
Refine Qtt;
Intros Qff;
Qrepl Qff;
Refine ih;
Save while_cond1;


Goal while_cond2 : {f:nat->bool}[lll=nat_iter zero ([a:nat]if (f (suc a)) (suc a) a)]
{n:nat}(Eq (lll n) n)\/(is_false (f (suc (lll n))));
intros f lll;
Refine nat_ind[n:nat](Eq (lll n) n)\/(is_false (f (suc (lll n))));
Refine inl (Eq_refl ?);
Intros n ih;
Refine ih;
Intros lnQn;
Refine true_or_false (f (suc (lll n)));
Intros Qtt;
Refine inl;
Expand lll nat_iter nat_rec;
Qrepl Qtt;
Refine Eq_resp suc lnQn;
Intros Qff;
Refine inr;
Expand lll nat_iter nat_rec;
Qrepl Qff;
Refine Qff;
Intros Qff;
Refine inr;
Expand lll nat_iter nat_rec;
Qrepl Qff;
Refine Qff;
Save while_cond2;

