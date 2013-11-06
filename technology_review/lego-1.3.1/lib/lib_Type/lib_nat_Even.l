Module lib_nat_Even Import lib_nat;

(* Contents
   --------
   o The datatype of even natural numbers.
*)

Even [m:nat] == {R:nat->Prop}
   (R zero) -> 
   ({n:nat}(R n) -> (R (suc (suc n)))) ->
   (R m);
(*
Inductive [Even : nat->Prop]
Constructors [ev1 : Even zero]
[ev2 : {n:nat}(Even n)->Even (suc (suc n))]; *)
(*
$[Even : nat->Prop];

$[ev1 : Even zero]
$[ev2 : {n:nat}(Even n)->Even (suc (suc n))];

[Even_elim : {T:nat->Type}
             (T zero)->
             ({n:nat}(T n)->T (suc (suc n)))->
                   {n:nat}(Even n)->T n];

[[T:nat->Type]
 [zero_case :T zero]
 [suc_suc_case :{n:nat}(T n)->T (suc (suc n))]
 [n:nat]
 [H:Even n]
    Even_elim T zero_case suc_suc_case zero ev1 ==> zero_case
 || Even_elim T zero_case suc_suc_case (suc (suc n)) (ev2 n H) ==> 
         suc_suc_case n (Even_elim T zero_case suc_suc_case n H)];
*)


Goal ev1 : Even zero;
Intros;
Immed;
Save ev1;

Goal ev2 : {n:nat}(Even n) -> (Even (suc (suc n)));
Intros;
Refine H2;
Refine H;
Immed;
Save ev2;


Goal Even_elim_nondep : {T:nat->Prop}
             (T zero)->
             ({n:nat}(T n)->T (suc (suc n)))->
                   {n:nat}(Even n)->T n;
intros;
Refine H2 T;
Immed;
Save Even_elim_nondep;

Goal Even_inv : {n:nat}(Even n)->
	((Eq n zero) \/ (Ex[x:nat](Eq n (suc (suc x))) /\ (Even x)));
Refine Even_elim_nondep[n:nat](Eq n zero)\/(Ex[x:nat](Eq n (suc (suc x)))/\(Even x));
Refine inl;
Refine Eq_refl;
intros n ih;
Refine inr;
Refine ExIntro n;
Refine pair;
Refine Eq_refl;
Refine ih;
intros;
Qrepl H;
Refine ev1;
intros;
Refine H;
intros;
Qrepl fst H1;
Refine ev2 ? (snd H1);
Save Even_inv;

Goal {n:nat}(Even (suc (suc n)))->(Even n);
intros;
Refine Even_inv ? H;
intros;
Refine zero_not_suc ? (Eq_sym H1);
intros;
Refine H1;
intros;
Qrepl Eq_resp pred (Eq_resp pred (fst H2));
Refine (snd H2);
Save Even_inv';
