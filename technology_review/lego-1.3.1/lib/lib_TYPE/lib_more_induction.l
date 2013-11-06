Module lib_more_induction Import lib_nat;

(* Contents
   --------
   o Some special induction principles on the natural numbers
*)


$[Rel [a,b:TYPE] = a -> b -> Prop];
$[Pred [a:TYPE] = a -> Prop];
Goal nat_iter_induction : {gamma|TYPE}{z|gamma}{s|gamma -> gamma}{phi:Pred gamma}
   (phi z) -> ({g:gamma}(phi g) -> (phi (s g))) ->
   [rec = nat_iter z s]{n:nat}phi (rec n);
Intros;Refine nat_elim [n:nat][rec = nat_iter z s]phi (rec n);
Immed;intros;Refine H1;Immed;
Save nat_iter_induction;


Goal nat_rec_induction : {gamma|TYPE}{z|gamma}{s|nat -> gamma -> gamma}{phi:Rel nat gamma}
   (phi zero z) -> ({m:nat}{g:gamma}(phi m g) -> (phi (suc m) (s m g))) ->
   [rec = nat_rec z s]{n:nat}phi n (rec n);
Intros;Refine nat_elim [n:nat][rec = nat_rec z s]phi n (rec n);
Immed;intros;Refine H1;Immed;
Save nat_rec_induction;


Goal nat_iter_induction_rev : {gamma|TYPE}{z|gamma}{s|gamma -> gamma}{phi:Pred gamma}{n:nat}
    (phi (nat_iter z s n))->({g:gamma}(phi (s g))->(phi g))->(phi z);
intros ____;
Refine nat_ind
  [n:nat](phi (nat_iter z s n))->({g:gamma}(phi (s g))->phi g)->phi z;
intros;
Refine H;
intros;
Refine H;
Refine H2;
Refine H1;
Refine H2;
Save nat_iter_induction_rev;

Discharge Rel; 












