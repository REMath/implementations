Module lib_list_Adjoin Import lib_list_length;

(* Contents
   --------
   o We define the relation Adjoin over lists and prove some of its 
     properties. 

   Changes
   -------

   19 Feb 1997 Thomas Schreiber <tms@dcs.ed.ac.uk>
               converted definition of Adjoin to a proper inductive relation
*)
(*
Notation :  We write -a-> and  -a^-1->  for 
(Adjoin a) and [xs,ys:list s]Adjoin a ys xs 

ad1 : xs --a--> a::xs

         xs --a--> ys    
ad2 : ------------------
      b::xs --a--> b::ys  
*)
Inductive [Adjoin : s->(list s)->(list s)->Prop] Relation
Parameters [s|Type]
Constructors [ad1:{a:s}{xs:list s}Adjoin a xs (cons a xs)]
[ad2:{xs|list s}{a|s}{axs|list s}(Adjoin a xs axs)
		-> {b:s} Adjoin a (cons b xs) (cons b axs)];




Goal Adjoin_inv : {a|s}{xs,ys|list s}(Adjoin a xs ys) -> 
	((Eq ys (cons a xs)) \/
 	 (Ex[xs':list s]Ex[ys':list s]Ex[c:s]
		 (Eq xs (cons c xs')) /\ (Eq ys (cons c ys'))
		 /\ (Adjoin a xs' ys')));
intros;
Equiv ([a:s][xs,ys:list s](Eq ys (cons a xs)) \/
	  (Ex[xs':list s]Ex[ys':list s]Ex[c:s]
		(Eq xs (cons c xs')) /\ (Eq ys (cons c ys'))
		/\ (Adjoin a xs' ys'))) a xs ys;
Refine Adjoin_elim;
  (* ad1 *)
  intros;Refine inl;Refine Eq_refl;
  (* ad2 *)
  intros;Refine inr; Refine ExIntro;Next +1; Refine ExIntro;Next +1;
  Refine ExIntro;Next +1;
  Refine pair; Refine pair; Refine Eq_refl; Refine Eq_refl; Try Immed; Try Immed;
Save Adjoin_inv;

Goal  Adjoin_inv_corr1 : {a,b|s}{xs,ys|list s}(Adjoin a (cons b xs) ys) -> 
	((Eq ys (cons a (cons b xs))) \/
	(Ex[ys':list s](Eq ys (cons b ys')) /\ (Adjoin a xs ys')));
intros; Refine Adjoin_inv H;
  intros;Refine inl;Try Immed;
  intros;Refine inr;Refine H1;intros;Refine H2;intros;Refine H3;intros;
  Refine H4;intros;Refine H5;intros;Refine ExIntro;Refine t1;
  Refine cons_inj H7;intros;andI;Equiv ([b:s]Eq ys (cons b t1)) b;
  Refine Eq_subst (Eq_sym H9);Try Immed;Equiv ([xs:list s]Adjoin a xs t1) xs;
  Refine Eq_subst (Eq_sym H10);Try Immed;
Save Adjoin_inv_corr1;

Goal  Adjoin_inv_corr2 : {a,b|s}{xs,ys|list s}(Adjoin a xs (cons b ys)) -> 
	(((Eq a b) /\ (Eq xs ys)) \/
	(Ex[xs':list s](Eq xs (cons b xs')) /\ (Adjoin a xs' ys)));
intros; Refine Adjoin_inv H;
  intros;Refine inl;Refine cons_inj H1;intros;andI;Refine Eq_sym;Try Immed;
  Refine Eq_sym;Try Immed;
  
  intros;Refine inr;Refine H1;intros;Refine H2;intros;Refine H3;intros;
  Refine H4;intros;Refine H5;intros;Refine ExIntro;Refine t;
  Refine cons_inj H8;intros;andI;Equiv ([b:s]Eq xs (cons b t)) b;
  Refine Eq_subst (Eq_sym H9);Try Immed;Refine Eq_subst (Eq_sym H10);Try Immed;
Save Adjoin_inv_corr2;

Goal  Adjoin_inv_corr3 : {a|s}{xs|list s}(Adjoin a (nil s) xs)
	 -> (Eq xs (cons a (nil s)));
intros; Refine Adjoin_inv H;
  intros;Try Immed;
  intros;Refine H1;intros;Refine H2;intros;Refine H3;intros;
  Refine H4;intros;Refine nil_not_cons ?? H5.fst;
Save Adjoin_inv_corr3;

Goal  Adjoin_inv_corr4 : {a|s}{xs|list s}(not (Adjoin a xs (nil s)));
intros;Intros H;Refine Adjoin_inv H;
  intros;Refine nil_not_cons ?? H1;
  intros;Refine H1;intros;Refine H2;intros;Refine H3;intros;
  Refine H4;intros;Refine H5;intros;Refine nil_not_cons ?? H8;
Save Adjoin_inv_corr4;

Goal Adjoin_inv_corr5 : {a|s}{xs|list s}(Adjoin a xs (cons a (nil s))) -> 
	(Eq xs (nil s));
intros; Refine Adjoin_inv H;
  intros;Refine cons_inj H1;intros;Refine Eq_sym H3;
  intros;Refine H1;intros;Refine H2;intros;Refine H3;intros;
  Refine H4;intros;Refine H5;intros;Refine Adjoin_inv_corr4;
  Next +2;Refine cons_inj H8;intros;Refine Eq_subst (Eq_sym H10);Try Immed;
Save Adjoin_inv_corr5;

(* The following lemmata prove that some diagrams commute in the category
   of relations over lists. 
*)

(* Adjoin_com :

   xs --a--> ys
    |         |
    b	      b
    |	      |
   zs --a--> us  
*)

Goal Adjoin_com1 : {a,b|s}{xs,us|list s}
	{ys|list s}(Adjoin a xs ys) -> (Adjoin b ys us)
     -> Ex[zs:list s](Adjoin b xs zs) /\ (Adjoin a zs us);
Intros a b xs us ys sd1;
Claim {us:list s}(Adjoin b ys us)->
  Ex ([zs:list s]and (Adjoin b xs zs) (Adjoin a zs us));
Refine ?+1;
Equiv ([a:s][xs,ys:list s]{us:list s}(Adjoin b ys us)
        ->Ex ([zs:list s]and (Adjoin b xs zs) (Adjoin a zs us))) a xs ys;
Refine Adjoin_elim; (* Induction over (Adjoin a xs ys) *)
  (* ad1 *)
  Intros a xs1 us sd2;
  Refine Adjoin_inv_corr1 sd2;Intros H;Refine ExIntro;Next +1;andI;Refine ad1;
  Refine Eq_subst (Eq_sym H);Refine ad2;Refine ad1;
  intros;Refine H;intros;Refine H1;intros;Refine ExIntro; Refine t;
  andI;Try Immed; Refine Eq_subst (Eq_sym H2);Refine ad1;
  (* ad2 *)
  intros;Refine Adjoin_inv_corr1 H;intros;Refine ExIntro;
  Refine cons b (cons b1 xs1);andI;Refine ad1; Qrepl H1;
  Refine ad2;Refine ad2;Try Immed;
  intros;Refine H1;intros; andE H2;Refine x1_ih t;Try Immed;intros;
  andE H5;Refine ExIntro;Refine cons b1 t1;andI;Refine ad2;
  Try Immed;Refine Eq_subst (Eq_sym H3);Refine ad2;Try Immed;
Try Immed;
Save Adjoin_com1;

(* Adjoin_com2 :

   xs --a--> ys
    |         |
    b^-1 =>  b^-1
    |	      |
   zs --a--> us  
*)

Goal Adjoin_com2 : {a,b|s}{xs,us|list s}
	{zs|list s}(Adjoin b zs xs) -> (Adjoin a zs us)
     -> Ex[ys:list s](Adjoin a xs ys) /\ (Adjoin b us ys);
Intros a b xs us zs sd1;
Claim {us:list s}(Adjoin a zs us)
     -> Ex[ys:list s](Adjoin a xs ys) /\ (Adjoin b us ys);
Refine ?+1;
Equiv ([b:s][zs,xs:list s]{us:list s}(Adjoin a zs us)
     ->Ex ([ys:list s]and (Adjoin a xs ys) (Adjoin b us ys)))b zs xs;
Refine Adjoin_elim;
  (* ad1 *)
  intros b1 zs1 us1 sd2;Refine Adjoin_inv sd2;
    (* inl *)
    intros;Refine ExIntro;Next +1;andI;Refine ad1;
    Equiv ([us1:list s]Adjoin b1 us1 (cons a (cons b1 zs1))) us1;
    Refine Eq_subst (Eq_sym H);Refine ad2;Refine ad1;
    (* inr *)
    intros;Refine H;intros zs' _;Refine H1;intros us' _;Refine H2;intros c _;
    Refine H3;intros;Refine H4;intros;
    Refine ExIntro;Next +1;andI;Refine ad2;Next +1;
    Equiv ([zs1:list s]Adjoin a zs1 ?+1)zs1;Refine Eq_subst (Eq_sym H6);
    Refine ad2;Next +1;Refine H5;
    Equiv ([us1:list s]Adjoin b1 us1 (cons b1 (cons c us'))) us1;
    Refine Eq_subst (Eq_sym H7);Refine ad1;
  (* ad2 *)
  intros zs b xs sd3 c IH us' sd4;Refine Adjoin_inv_corr1 sd4;intros;
    (* inl *)
    Refine ExIntro;Next +1;andI;Refine ad1;
    Equiv ([us':list s]Adjoin b1 us' (cons a (cons c xs1))) us';
    Refine Eq_subst (Eq_sym H);Refine ad2;Refine ad2;Try Immed;
    (* inr *)
    intros;Refine H;intros us'' _;Refine H1;intros;Refine IH us'';
    Try Immed;intros us _;Refine H4;intros;Refine ExIntro;Next +1;andI;
    Refine ad2;Try Immed;Equiv ([us':list s]Adjoin b1 us' (cons c us1)) us';
    Refine Eq_subst (Eq_sym H2);Refine ad2;Try Immed;
Try Immed;
Save Adjoin_com2;

(* Adjoin_com3 : xs = us \/

   xs --a--> ys
    |         |
   b^-1 <=   b^-1
    |	      |
   zs --a--> us 
*)

Goal Adjoin_com3 : {a,b|s}{xs,us|list s}
	{ys|list s}(Adjoin a xs ys) -> (Adjoin b us ys)
     -> (((Eq us xs) /\ (Eq b a)) \/ 
 	(Ex[zs:list s](Adjoin b zs xs) /\ (Adjoin a zs us)));
intros;
Claim {us:list s}(Adjoin b us ys)
     -> (((Eq us xs) /\ (Eq b a)) \/ 
 	(Ex[zs:list s](Adjoin b zs xs) /\ (Adjoin a zs us)));
Refine ?+1;Try Immed;
Equiv ([a:s][xs,ys:list s]{us:list s}(Adjoin b us ys)
     -> (((Eq us xs) /\ (Eq b a)) \/ 
 	(Ex[zs:list s](Adjoin b zs xs) /\ (Adjoin a zs us)))) a xs ys;
Refine Adjoin_elim;
  (* ad1 *)
  intros;Refine Adjoin_inv_corr2 H2;
    (* inl *)
    intros;Refine H3;intros;Refine inl;andI;Try Immed;
    (* inr *)
    intros;Refine H3;intros us' _;Refine H4;intros;Refine inr;Refine ExIntro;
    Next +1;andI;Try Immed;Refine Eq_subst (Eq_sym H5);Refine ad1;
  (* ad2 *)
  intros xs1 b1 zs1 s1 c IH us' s2;Refine Adjoin_inv_corr2 s2;
    (* inl *)
    intros;Refine H2;intros;Refine inr;Refine ExIntro;Next +1;andI;
    Equiv ([b:s]Adjoin b ?+2 (cons c xs1))b;Refine Eq_subst (Eq_sym H3);
    Refine ad1;Refine Eq_subst (Eq_sym H4);Try Immed;
    (* inr *)
    intros;Refine H2;intros us'' _;Refine H3;intros;Refine IH us'';Try Immed;
      (* inl *)
      intros;Refine inl;Refine H6;intros;andI;
      Equiv ([us':list s]Eq us' (cons c xs1))us';Refine Eq_subst (Eq_sym H4);
      Refine Eq_resp;Try Immed;
      (* inr *)
      intros;Refine H6;intros ys _;Refine H7;intros;Refine inr;Refine ExIntro;
      Next +1;andI;Refine ad2;Try Immed;Refine Eq_subst (Eq_sym H4);Refine ad2;
      Try Immed;
Try Immed;
Save Adjoin_com3;

Goal Adjoin_length_suc : {a|s}{l,al|list s}(Adjoin a l al)->(Eq (length al) (suc (length l)));
Refine Adjoin_elim [a:s][l,al:list s]Eq (length al) (suc (length l));
intros;
Refine Eq_refl;
intros;
Refine Eq_resp suc; Try Immed;
Save Adjoin_length_suc;

Discharge s;


