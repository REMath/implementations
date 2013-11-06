Module lib_list_Perm Import lib_list_Distin;

(* 
Contents
--------

We define the relation Perm over lists (~) and prove some of its properties.
In particular the following properties of Perm are derivable :

1.) ~ is an equivalence (Perm_refl,Perm_sym,Perm_trans 

        xs ~ ys
2.) ------------- (Perm_fact)
    a::xs ~ a::ys

    a::xs ~ a::ys
3.) ------------- (Perm_Adjoin_com2_corr)
       xs ~ ys  

perm1 : [] ~ []

	xs' <--a-- xs ~ ys --a--> ys'
perm2 : -----------------------------
        	  xs' ~ ys'                        

Changes
-------

20 Feb 97 Thomas Schreiber <tms@dcs.ed.ac.uk>
  - Perm is now a proper inductive relation
  - simplified proof of Perm_Adjoin_com3
*)

Inductive [Perm:(list s)->(list s)->Prop] Relation 
Parameters [s|Type]
Constructors [perm1:Perm (nil s) (nil s)]
[perm2:{xs,ys:list s}(Perm xs ys)
	    -> {a:s}{axs:list s}(Adjoin a xs axs) 
	         -> {ays:list s}(Adjoin a ys ays) 
            -> (Perm axs ays)];

Goal Perm_fact : {xs,ys|list s}{a|s}(Perm xs ys) -> (Perm (cons a xs) (cons a ys));
intros;Refine perm2;Next +2;Refine H;Next +1;Refine ad1;Refine ad1;
Save Perm_fact;

Goal Perm_refl : {xs:list s}Perm xs xs;
intros;
Refine list_ind [xs:list s]Perm xs xs;
  (* nil *)
  Refine perm1;
  (* cons *)
  intros;Refine perm2;Try Immed;Refine ad1;Refine ad1;
Save Perm_refl;

Goal Perm_sym : {xs,ys|list s}(Perm xs ys) -> (Perm ys xs);
intros;
Refine Perm_elim [xs,ys:list s]Perm ys xs;
  (* perm1 *)
  Refine perm1;
  (* perm2 *)
  intros;Refine perm2 ys1 xs1;Try Immed;
Try Immed;
Save Perm_sym;

(* Perm_Adjoin_com1 :

  vs ~ xs -a-> ys <-a- zs
  -----------------------
  	vs ~ zs  		*)

Goal Perm_Adjoin_com1 : {a|s}{vs,xs,ys,zs|list s}
	(Perm vs xs) -> (Adjoin a xs ys) -> (Adjoin a zs ys) ->
	(Perm vs zs);
intros a vs xs ys zs P1;
Claim {ys,zs:list s}(Adjoin a xs ys) -> (Adjoin a zs ys) ->
	(Perm vs zs);
Refine ?+1;
Equiv ([vs,xs:list s] {ys,zs:list s}(Adjoin a xs ys)->(Adjoin a zs ys)
	->Perm vs zs) vs xs;
Refine Perm_elim;
  (* perm1 *)
  intros;Claim Eq zs1 (nil s);Refine Eq_subst (Eq_sym ?+1);Refine perm1;
  Refine Adjoin_inv_corr5;Next +1;Claim Eq ys1 (cons a (nil s));
  Refine Eq_subst ?+2;Try Immed;Refine Adjoin_inv_corr3;Try Immed;
  (* perm2 *)
  intros vs1 xs1 P2 c vs' s1 xs' s2 IH ys' zs' s3 s4;
  Refine Adjoin_com1 s2 s3;
  intros ys'' _;Refine H;intros;Refine Adjoin_com3 H2 s4;
    (* inl *)
    intros;Refine H3;intros;Refine Eq_subst (Eq_sym H4);Refine perm2;Next +2;
    Refine P2;Refine c;Try Immed;Equiv ([c:s]Adjoin c xs1 ys'')c;
    Refine Eq_subst H5;Try Immed;
    (* inr *)
    intros;Refine H3;intros zs'' _;Refine H4;intros;Refine perm2;Next +2;
    Refine IH ys'' zs'';Try Immed;
Try Immed;
Save Perm_Adjoin_com1;

(* Perm_Adjoin_com2 :

   xs --a--> ys ~ zs <--a-- us
   ---------------------------
	     xs ~ us		*)

Goal Perm_Adjoin_com2 : {a|s}{xs,ys,zs,us|list s}(Adjoin a xs ys) -> (Perm ys zs) 
	-> (Adjoin a us zs) -> (Perm xs us);
intros;
Claim {xs,us:list s}(Adjoin a xs ys) -> (Adjoin a us zs) -> (Perm xs us);
Refine ?+1;Try Immed;
Equiv ([ys,zs:list s]{xs,us:list s}
	(Adjoin a xs ys)->(Adjoin a us zs)->Perm xs us) ys zs;
Refine Perm_elim;
  (* perm1 *)
  intros;Refine Adjoin_inv_corr4;Try Immed;
  (* perm2 *)
  intros ys zs P1 b ys' s1 zs' s2 IH xs' us' s3 s4;Refine Adjoin_com3 s1 s3;
    (* inl *)
    intros;Refine H3;intros;Equiv ([xs':list s]Perm xs' us')xs';
    Refine Eq_subst (Eq_sym H4);Refine Perm_Adjoin_com1;Next +3;Refine P1;
    Next +2;Refine s2;Equiv ([b:s]Adjoin b us' zs')b;Refine Eq_subst H5;
    Try Immed;
    (* inr *)
    intros;Refine H3;intros xs1 _;Refine H4;intros;
    Refine Adjoin_com3 s2 s4;
      (* inl *)
      intros;Refine H7;intros;Refine Eq_subst (Eq_sym H8);Refine Perm_sym;
      Refine Perm_Adjoin_com1;Next +3;Refine Perm_sym P1;Next +2;
      Refine s1;Equiv ([b:s]Adjoin b xs' ys') b;Refine Eq_subst H9;
      Try Immed;
      (* inr *)
      intros;Refine H7;intros us1 _;Refine H8;intros;
      Refine perm2;Next +2;Refine IH xs1 us1;Try Immed;
Try Immed;
Save Perm_Adjoin_com2;

Goal Perm_Adjoin_com2_corr :
  {a|s}{xs,ys|list s}(Perm (cons a xs) (cons a ys)) -> (Perm xs ys);
Intros;Refine Perm_Adjoin_com2;Next +4;Refine H;Next +1;Refine ad1;Refine ad1;
Save Perm_Adjoin_com2_corr;

(* Perm_Adjoin_com3

  xs  ~  us
   |      |
   a  =>  a
   |      |
  ys  ~  zs  *)

Goal Perm_Adjoin_com3 : {a|s}{xs,zs|list s}{ys|list s}(Adjoin a xs ys) -> (Perm ys zs) 
	-> Ex[us:list s](Perm xs us) /\ (Adjoin a us zs);
intros;
Claim {xs:list s}(Adjoin a xs ys)
	-> Ex[us:list s](Perm xs us) /\ (Adjoin a us zs);
Refine ?+1;Try Immed;
Equiv ([ys,zs:list s]{xs:list s}(Adjoin a xs ys)
	->Ex ([us:list s]and (Perm xs us) (Adjoin a us zs))) ys zs;
Refine Perm_elim;
  (* perm1 *)
  intros;Refine Adjoin_inv_corr4;Next +2;Try Immed;
  (* perm2 *)
  intros ys1 zs1 _ b ys' s1 zs' s2 IH xs' s3;Refine Adjoin_com3 s1 s3;
    (* inl *)
    intros;andE H2;Refine ExIntro;Next +1;andI;
    Equiv ([xs':list s]Perm xs' ?+2) xs'; Qrepl H3; Assumption;
    Qrepl H4; Assumption;
    (* inr *)
    intros H0;Refine H0;intros xs _;andE H2;Refine IH xs1;Try Immed;
    intros us _;andE H5;Refine Adjoin_com1 H7 s2;Intros us' _;
    andE H8;Refine ExIntro;Refine us';andI;Refine perm2;Next +2;
Try Immed; Try Immed;
Save Perm_Adjoin_com3;

Goal Perm_trans :
  {xs,ys,zs|list s}(Perm xs ys) -> (Perm ys zs) -> (Perm xs zs);
intros xs ys zs P1;
Claim {zs:list s}(Perm ys zs) -> (Perm xs zs);Refine ?+1;
Equiv ([xs,ys:list s]{zs:list s}(Perm ys zs)->Perm xs zs) xs ys;
Refine Perm_elim;
  (* perm1 *)
  intros;Try Immed;
  (* perm2 *)
  intros xs1 ys1 P2 a xs' s1 ys' s2 IH zs' P3;
  Refine Perm_Adjoin_com3 s2 P3;intros zs'' _;Refine H;intros;
  Refine perm2;Next +2;Refine IH zs'';Try Immed;
Try Immed;
Save Perm_trans;

Goal Perm_of_Distin : {xs,ys:list s}(Distin xs)->({a:s}(Member a xs)->(Member a ys))->
(Eq (length xs) (length ys))->(Perm xs ys);
Refine list_ind [xs:list s]{ys:list s}(Distin xs)->({a:s}(Member a xs)->
(Member a ys))->(Eq (length xs) (length ys))->(Perm xs ys);
intros;
Qrepl length_zero_nil ? (Eq_sym H2);
Refine perm1;
intros;
Refine H2 x;
Refine ExIntro l;
Refine ad1;
intros;
Refine perm2 l t ? x;
Refine H;
Refine snd (Distin_inv H1);
intros b _;
Refine Member_Adjoin ? H4;
Intros _;
Refine fst (Distin_inv H1);
Qrepl H6;
Refine H5;
Refine H2 b;
Refine snd (Mem_ind|?|?|?|?);
Refine inl H5;
Refine Eq_resp pred|(length (cons x l))|(suc (length t));
Qrepl H3;
Refine Adjoin_length_suc H4;
Refine ad1;
Refine H4;
Save Perm_of_Distin;

Goal surjective_imp_Perm : {l:list s}{f,g:s->s}(Distin l)->({x:s}(Member x l)->(Member (g x) l))->
({x:s}Eq (f (g x)) x)->(Perm l (map f l));
intros;
Refine Perm_of_Distin;
Refine H;
intros;
Qrepl Eq_sym (H2 a);
Refine Member_map;
Refine H1 a H3;
Refine Eq_sym (length_map ??);
Save surjective_imp_Perm;

Discharge s;
