Module lib_list_Member Import lib_list_Adjoin
                              lib_list_prod;
         
(*     "lib_nat/lib_nat_Prop_rels"   get rid of this.... *)

(* Contents
   --------
   o A new definition "Member" of list membership based on "Adjoin"
   o Several theorems about this definition
*)

[s,u|SET];

Member == [a:s][xs:list s]Ex([ys:list s]Adjoin a ys xs);

Goal not_Member_nil : {a|s}not (Member a (nil s));
Intros __;
Refine H;
intros;
Refine Adjoin_inv_corr4 H1;
Save not_Member_nil;

Goal Mem_ind : {l|list s}{a,b|s}iff (Member b (cons a l)) ((Member b l)\/(Eq a b));
intros;
Refine pair;
intros;
Refine H;
intros;
Refine Adjoin_inv_corr2 H1;
intros;
Refine inr (Eq_sym (fst H2));
intros;
Refine inl;
Refine H2;
intros;
Refine ExIntro t1;
Refine snd H3;
intros;
Refine H;
intros;
Refine H1;
intros;
Refine ExIntro (cons a t);
Refine ad2 H2;
intros;
Qrepl H1;
Refine ExIntro l;
Refine ad1;
Save Mem_ind;

DischargeKeep s;

Goal Member_Adjoin : {l,al|list s}{a,b|s}~(Eq a b)->(Adjoin a l al)->(Member b al)->(Member b l);
intros;
Refine H2;
intros;
Refine Adjoin_com3 H1 H3;
intros;
Refine H (Eq_sym (snd H4));
intros;
Refine H4;
intros;
Refine ExIntro t1;
Refine fst H5;
Save Member_Adjoin;

Goal Member_map : {l:list s}{a:s}{f:s->u}(Member a l)->Member (f a) (map f l);
Refine list_ind[l:list s]{a:s}{f:s->u}(Member a l)->Member (f a) (map f l);
intros;
Refine not_Member_nil H;
intros;
Refine snd (Mem_ind|?|?|?|?);
Refine fst (Mem_ind|?|?|?|?) H1;
intros;
Refine inl;
Refine H ?? H2;
intros;
Refine inr;
Refine Eq_resp f H2;
Save Member_map;

Goal Member_map_inv : {l:list s}{b:u}{f:s->u}(Member b (map f l))->Ex[a:s](Member a l)/\(Eq (f a) b);
Refine list_ind[l:list s]{b:u}{f:s->u}(Member b (map f l))->Ex[a:s](Member a l)/\(Eq (f a) b);
intros;
Refine not_Member_nil H;
intros;
Refine fst (Mem_ind|?|?|?|?) H1;
intros;
Refine H ?? H2;
intros;
Refine ExIntro t;
Refine pair ? (snd H3);
Refine snd (Mem_ind|?|?|?|?) (inl (fst H3));
intros;
Refine ExIntro x;
Refine pair ? H2;
Refine snd (Mem_ind|?|?|?|?) (inr (Eq_refl ?));
Save Member_map_inv;

Goal Member_append : {l1,l2:list s}{a:s}iff (Member a (append l1 l2)) ((Member a l1)\/(Member a l2));
intros;
Refine list_ind[l1:list s]iff (Member a (append l1 l2)) ((Member a l1)\/(Member a l2));
Refine pair;
Refine inr;
intros;
Refine H;
intros;
Refine not_Member_nil H1;
Refine PropId;
intros;
Refine pair;
intros;
Refine fst (Mem_ind|?|?|?|?) H1;
intros;
Refine fst H H2;
intros;
Refine inl;
Refine snd (Mem_ind|?|?|?|?) (inl H3);
Refine inr;
intros;
Refine inl;
Refine snd (Mem_ind|?|?|?|?) (inr H2);
intros;
Refine snd (Mem_ind|?|?|?|?);
Refine H1;
intros;
Refine fst (Mem_ind|?|?|?|?) H2;
intros;
Refine inl;
Refine snd H (inl H3);
Refine inr;
intros;
Refine inl;
Refine snd H (inr H2);
Save Member_append;

DischargeKeep s;

Goal Member_prod : {l1:list s}{l2:list u}{p:prod s u}iff (Member p (prod_list l1 l2)) 
((Member (Fst p) l1)/\(Member (Snd p) l2));
intros;
Refine list_ind[l1:list s]iff (Member p (prod_list l1 l2)) ((Member (Fst p) l1)/\(Member (Snd p) l2));
Refine pair;
intros;
Refine not_Member_nil H;
intros;
Refine not_Member_nil (fst H);
intros;
Refine pair;
intros;
Refine fst (Member_append ???) H1;
intros;
Refine Member_map_inv ??? H2;
intros;
Refine pair;
Refine snd (Mem_ind|?|?|?|?) (inr ?);
Refine Eq_resp (Fst|s|u) (snd H3);
Qrepl Eq_sym (Eq_resp (Snd|s|u) (snd H3));
Refine fst H3;
intros;
Refine fst H H2;
intros;
Refine pair (snd (Mem_ind|?|?|?|?) (inl H3)) H4;
intros;
Refine snd (Member_append ???);
Refine fst (Mem_ind|?|?|?|?) (fst H1);
intros;
Refine inr;
Refine snd H (pair H2 (snd H1));
intros;
Refine inl;
Qrepl prod_eta p;
Qrepl H2;
Refine Member_map ??? (snd H1);
Save Member_prod;

Goal ll_logic : {A,B,C,D,E|Prop}(iff B C)->(iff D (B\/A))->(iff E (C\/A))->(iff D E);
intros;
Refine pair;
intros;
Refine snd H2;
Refine fst H1 H3;
intros;
Refine inl (fst H H4);
Refine inr;
intros;
Refine snd H1;
Refine fst H2 H3;
intros;
Refine inl (snd H H4);
Refine inr;
$Save ll_logic;

Goal Member_build : {f:nat->s}{n:nat}{a:s}iff (Member a (build_list f n))
(Ex [k:nat](Lt k n)/\(Eq (f k) a));
intros;
Refine nat_ind [n:nat]iff (Member a (build_list f n)) (Ex [k:nat](Lt k n)/\(Eq (f k) a));
Refine pair;
intros;
Refine not_Member_nil H;
intros;
Refine H;
intros;
Refine not_n_Lt_zero ? (fst H1);
intros;
Refine ll_logic H (Mem_ind|?|?|?|?) (exists_suc ([x:nat]Eq (f x) a) ?);
Save Member_build;

Discharge s;



(* Memo: can we move exists_suc into lib_nat_Lt from
   lib_nat_Prop_rels, because then we don't have
   this stupid dependency on Le *)



