Module lib_list_Distin Import lib_list_Member
                              lib_nat_Le;

(* Contents
   --------
   o Definition of the property "Distin" of lists, which is satisfied by  
     lists whose elements are all distinct.
   o Theorems about this property.

   Changes
   -------
   19 Feb 97 Thomas Schreiber <tms@dcs.ed.ac.uk>
      - Distin is now a proper inductive relation
      - simplified prove of Distin_inv
*)

Inductive [Distin : (list s)->Prop] Parameters [s|Type] Relation
Constructors 
[Dis1   : Distin (nil s)]
[Dis2   : {a:s}{xs:list s}~(Member a xs)->(Distin xs)->(Distin (cons a xs))];

DischargeKeep s;
[u|Type];

Goal Distin_inv : {a|s}{l|list s}(Distin (cons a l))->
	(~(Member a l) /\ (Distin l));
intros __;
Refine Distin_elim [l:list s](~(Member (hd a l) (tail l)) /\ (Distin (tail l)));
Refine pair;
Refine not_Member_nil;
Refine Dis1;
intros;
Refine pair; Try Immed;
Save Distin_inv;

Goal Distin_append : {l1,l2:list s}(Distin l1)->(Distin l2)->
     ({a:s}(Member a l1)->~(Member a l2))->Distin (append l1 l2);
Induction 1;

  (** first case **)
  Induction 1;

    (** Case 1.1 **)
    intros; Refine Dis1;

    (** Case 1.2 **)
    intros; Refine Dis2; Try Immed;

  (** second case **)
    intros; Refine Dis2;
      Intros _; Refine fst (Member_append ???) H2; Try Immed;
        Refine H1; Refine snd (Mem_ind|?|?|?|?) (inr (Eq_refl ?));
      Refine x2_ih; Try Immed; Intros el __; Refine H1; Try Immed;
        Refine snd (Mem_ind|?|?|?|?) (inl ?); Try Immed;
Save Distin_append;

Goal Distin_inj_map :
  {l:list s}{f:s->u}({a1,a2:s}(Member a1 l)->(Member a2 l)->
  (Eq (f a1) (f a2))->(Eq a1 a2))->(Distin l)->(Distin (map f l));

Induction 2;

  (** base case **)  
  intros; Refine Dis1;

  (** step case **)
  intros;
  Refine Dis2;

    Intros _;
    Refine Member_map_inv ??? H;
    intros; andE H1;
    Refine x1; Claim Eq a t; Qrepl ?-0; Try Immed;
    Refine x3;
    Refine snd (Mem_ind|?|?|?|?) (inr (Eq_refl ?));
    Refine snd (Mem_ind|?|?|?|?) (inl ?); Try Immed;
    Refine Eq_sym; Try Immed;

    Refine x2_ih; intros ____; Refine x3;
    Refine snd (Mem_ind|?|?|?|?) (inl ?); Assumption;
    Refine snd (Mem_ind|?|?|?|?) (inl ?); Assumption;
Save Distin_inj_map;

DischargeKeep s;

Goal Distin_prod :
  {l1:list s}{l2:list u}(Distin l1)->(Distin l2)->Distin (prod_list l1 l2);
Induction 1;

  (** base case **)
  intros; Refine Dis1;

  (** step case **)
  intros;
  Refine Distin_append;
  Refine Distin_inj_map;
  intros;
  Refine Eq_resp (Snd|s|u) H3;
  Assumption;
  Refine x2_ih; Assumption;
  intros;
  Refine Member_map_inv ??? H1;
  intros;
  Qrepl Eq_sym (snd H2);
  Intros _;
  Refine fst (Member_prod ???) H3;
  intros;
  Refine x1; Try Immed;
Save Distin_prod;

Goal Distin_inj_build :
  {f:nat->s}{n:nat}({k1,k2:nat}(Lt k1 n)->(Lt k2 n)->
  (Eq (f k1) (f k2))->(Eq k1 k2))->Distin (build_list f n);
intros f;
Refine nat_ind [n:nat]({k1,k2:nat}(Lt k1 n)->(Lt k2 n)->(Eq (f k1) (f k2))->Eq k1 k2)->Distin (build_list f n);
intros;
Refine Dis1;
intros;
Refine Dis2;
Refine +1 H;
Equiv not (Member (f n) (build_list f ?));
Intros _;
Refine (fst (Member_build|? f n (f n))) H2;
intros;
Refine not_refl_Lt n;
Claim Eq t n;
Refine Eq_subst ?+1 ([b:nat](Lt b n));
Refine fst H3;
Refine H1;
Refine Lt_trans; Refine +1 fst H3;
Refine n_Lt_suc_n;
Refine n_Lt_suc_n;
Refine snd H3;
intros;
Refine H1;
Refine Lt_trans; Refine +1 H2;
Refine n_Lt_suc_n;
Refine Lt_trans; Refine +1 H3;
Refine n_Lt_suc_n;
Refine H4;
Save Distin_inj_build;

Goal Distin_sublist_Le_length :
  {xs,ys:list s}(Distin xs)->({a:s}(Member a xs)->(Member a ys))->
  (Le (length xs) (length ys));

Induction 1;

  (** base case **)
  intros;
  Refine Le_zero_n;

  (** step case **)
  intros;
  Refine H a;
    Refine snd (Mem_ind|?|?|?|?) (inr (Eq_refl ?));
    intros;
      Qrepl Adjoin_length_suc H1;
      Refine Le_resp_suc;
      Refine x2_ih;
      intros;
      Refine Member_Adjoin ? H1;
        Intros _; Refine x1; Qrepl H3; Assumption;
	Refine H; Refine snd (Mem_ind|?|?|?|?) (inl ?); Assumption;
Save Distin_sublist_Le_length;

Discharge s;










