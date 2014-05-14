Module lib_bool_thms Import lib_bool_funs;

(* Contents
   --------
   o Various theorems about boolean functions.

   Changes
   -------
   Thomas Schreiber <tms@dcs.ed.ac.uk>
     o added inv_character' and inv_idemp; notice that
       inv_is_true_is_false and inv_is_false_is_true are corollaries of
       inv_character' 

*)

Goal is_true_not_is_false : {b:bool}iff (is_true b) (not (is_false b));
intros; Refine pair;
intros h; Qrepl h; Refine true_not_false;
intros h; Refine true_or_false b; intros; Immed; intros; Refine h; Immed;
Save is_true_not_is_false;

Goal bool_contrapos : {a,b|bool}((is_true a)->(is_true b))->(is_false b)->(is_false a);
Expand is_true is_false;
Refine bool_double_elim [a,b|bool]((Eq a true)->Eq b true)->(Eq b false)->Eq a false;
intros; Immed;
intros h j; Refine Eq_sym (h (Eq_refl true));
intros; Refine Eq_refl;
intros; Refine Eq_refl;
Save bool_contrapos;

(* proof by contradiction *)
Goal bool_contradiction : {b|bool}(is_true b)->(is_false b)->absurd;
intros; Refine true_not_false; Qrepl Eq_sym H; Qrepl Eq_sym H1; Refine Eq_refl;
Save bool_contradiction;

(* if *)
Goal if_absorbs : {b:bool}{t|SET}{x:t}Eq (if b x x) x;
intros; Refine bool_elim [b:bool]Eq (if b x x) x;
Refine Eq_refl;
intros; Refine Eq_refl;
Save if_absorbs;


Goal if_character : {t|SET}{x,y,z|t}{b|bool}(Eq (if b x y) z)->or (Eq x z) (Eq y z);
intros ____;
Refine bool_elim [b'|bool](Eq (if b' x y) z)->or (Eq x z) (Eq y z);
intros; Refine inl; Immed;
intros; Refine inr; Immed;
Save if_character;


Goal Eq_resp_if : {t|SET}{x,y,x',y'|t}(Eq x x')->(Eq y y')->
                   {b:bool}Eq (if b x y) (if b x' y');
intros; Refine true_or_false b;
intros trueb; Qrepl trueb; Expand if; Refine H;
intros falseb; Qrepl falseb; Expand if; Refine H1;
Save Eq_resp_if;


(* moving if inside *)
Goal if_inside : {s,t|SET}{f:s->t}{x,y:s}{b:bool}Eq (if b (f x) (f y)) (f (if b x y));
intros; Refine true_or_false b;
intros trueb; Qrepl trueb; Refine Eq_refl;
intros falseb; Qrepl falseb; Refine Eq_refl;
Save if_inside;

Goal middle_four_if : {A|SET}{a,b,c,d:A}{x,y:bool}Eq (if x (if y a b) (if y c d))
                                  (if y (if x a c) (if x b d));
intros; Refine true_or_false x;
intros ttx; Qrepl ttx; Refine Eq_refl;
intros ffx; Qrepl ffx; Refine Eq_refl;
Save middle_four_if;

Goal reduce_if_left : {A|SET}{a,b,c:A}{x:bool}Eq (if x (if x a b) c) (if x a c);
intros; Refine true_or_false x;
intros ttx; Qrepl ttx; Refine Eq_refl;
intros ffx; Qrepl ffx; Refine Eq_refl;
Save reduce_if_left;

Goal reduce_if_right : {A|SET}{a,b,c:A}{x:bool}Eq (if x a (if x b c)) (if x a c);
intros; Refine true_or_false x;
intros ttx; Qrepl ttx; Refine Eq_refl;
intros ffx; Qrepl ffx; Refine Eq_refl;
Save reduce_if_right;

Goal if_prop : {C|SET}{b:bool}((Eq b true)->C)->((Eq b false)->C)->C;
intros __;
Refine bool_elim [b:bool]((Eq b true)->C)->((Eq b false)->C)->C;
intros;
Refine H;
Refine Eq_refl;
intros;
Refine H1;
Refine Eq_refl;
Save if_prop;

(* andalso *)
Goal andalso_character : {a,b:bool}iff (is_true (andalso a b)) (and (is_true a) (is_true b));
intros; Refine pair;
intros h; Refine true_or_false a; intros atrue; Refine true_or_false b;
intros btrue; Refine pair atrue btrue;
intros bfalse; Refine true_not_false; Qrepl Eq_sym h;
    Qrepl atrue; Qrepl bfalse; Refine Eq_refl;intros afalse; 
Refine true_not_false; Qrepl Eq_sym h; Qrepl afalse; Refine Eq_refl;
intros atruebtrue; Qrepl fst atruebtrue; Qrepl snd atruebtrue; Refine Eq_refl;
Save andalso_character;


Goal andalso_absorbs : {b:bool}Eq (andalso b b) b;
intros; Refine true_or_false b;
intros trueb; Qrepl trueb; Refine Eq_refl;
intros falseb; Qrepl falseb; Refine Eq_refl;
Save andalso_absorbs;

Goal andalso_commutes : {b,c:bool}Eq (andalso b c) (andalso c b);
 Refine bool_double_elim [b,c:bool]Eq (andalso b c) (andalso c b);
 Refine Eq_refl;
 Refine Eq_refl;
 Refine Eq_refl;
 Refine Eq_refl;
Save andalso_commutes;


Goal andalso_false : {b:bool}Eq (andalso b false) false;
 Refine bool_ind [b:bool]Eq (andalso b false) false;
 Refine Eq_refl;
 Refine Eq_refl;
Save andalso_false;


Goal andalso_true : {b:bool}Eq (andalso b true) b;
 Refine bool_ind [b:bool]Eq (andalso b true) b;
 Refine Eq_refl;
 Refine Eq_refl;
Save andalso_true;


(* inv *)
Goal inv_character : {b:bool}iff (is_true (inv b)) (not (is_true b));
intros; Refine pair;
Intros h g; Refine true_not_false; Qrepl Eq_sym h; Qrepl g; Refine Eq_refl;
intros notbtrue; Refine true_or_false b;
intros; Refine notbtrue; Immed;
intros bfalse; Qrepl bfalse; Refine Eq_refl;
Save inv_character;

Goal inv_character' : {a,b:bool}iff (Eq (inv a) b) (Eq a (inv b));
Refine bool_elim [a:bool]{b:bool}iff (Eq (inv a) b) (Eq a (inv b));
  intros; 
  Refine pair;
    intros; Qrepl Eq_sym H; Refine Eq_refl;
    Refine bool_elim [b:bool](Eq true (inv b))->Eq (inv true) b;
      Refine Eq_sym;
      intros; Refine Eq_refl;
  intros;
  Refine pair;
  intros; Qrepl Eq_sym H; Refine Eq_refl;
  Refine bool_elim [b:bool](Eq false (inv b))->Eq (inv false) b;
    intros; Refine Eq_refl;
    Refine Eq_sym;
Save;


Goal inv_idemp : {b:bool}Eq (inv (inv b)) b;
intros;
Refine bool_ind [b:bool]Eq (inv (inv b)) b;
Refine Eq_refl; Refine Eq_refl;
Save;

Goal inv_is_true_is_false : {n:bool} iff (is_true (inv n)) (is_false n);
Refine bool_ind [n:bool] iff (is_true (inv n)) (is_false n);
andI;
Expand is_true;
Expand is_false;
Refine Eq_sym;
Expand is_true;
Refine Eq_sym;
andI;
intros;
Refine Eq_refl;
intros;
Refine Eq_refl;
Save inv_is_true_is_false;

Goal inv_is_false_is_true : {n:bool} iff (is_false (inv n)) (is_true n);
Refine bool_ind [n:bool]iff (is_false (inv n)) (is_true n);
andI; intros; Refine Eq_refl; intros; Refine Eq_refl;
andI; 
intros; Refine Eq_sym; Immed;
intros; Refine Eq_sym; Immed;
Save inv_is_false_is_true;

(* orelse *)
Goal orelse_character : {a,b:bool}iff (is_true (orelse a b)) (or (is_true a) (is_true b));
intros; Refine pair;
intros orelseab; Refine true_or_false a; intros atrue; Refine inl atrue;
intros afalse; Refine inr;  Expand is_true;
Qrepl Eq_sym orelseab; Qrepl afalse; Refine Eq_refl;
intros orab; Refine orab;
intros atrue; Expand is_true; Qrepl atrue; Refine Eq_refl;
intros btrue; Expand is_true; Qrepl btrue; Refine true_or_false a;
intros atrue; Expand is_true; Qrepl atrue; Refine Eq_refl;
intros afalse; Expand is_true; Qrepl afalse; Refine Eq_refl;
Save orelse_character;


Goal orelse_absorbs : {b:bool}Eq (orelse b b) b;
intros; Refine true_or_false b;
intros trueb; Qrepl trueb; Refine Eq_refl;
intros falseb; Qrepl falseb; Refine Eq_refl;
Save orelse_absorbs;


Goal orelse_assoc : {a,b,c:bool}Eq (orelse (orelse a b) c) (orelse a (orelse b c));
intros;
Refine true_or_false a;
intros truea; Qrepl truea; Refine Eq_refl;
intros falsea; Qrepl falsea; Refine Eq_refl;
Save orelse_assoc;


Goal orelse_commutes : {a,b:bool}Eq (orelse a b) (orelse b a);
intros;
Refine true_or_false a;
intros ah; Qrepl ah;
Refine true_or_false b;
intros bh; Qrepl bh; Refine Eq_refl;
intros bh; Qrepl bh; Refine Eq_refl;
intros ah; Qrepl ah;
Refine true_or_false b;
intros bh; Qrepl bh; Refine Eq_refl;
intros bh; Qrepl bh; Refine Eq_refl;
Save orelse_commutes;



Goal orelse_false : {b:bool}Eq (orelse b false) b;
 Refine bool_ind [b:bool]Eq (orelse b false) b;
 Refine Eq_refl;
 Refine Eq_refl;
Save orelse_false;


Goal orelse_true : {b:bool}Eq (orelse b true) true;
 Refine bool_ind [b:bool]Eq (orelse b true) true;
 Refine Eq_refl;
 Refine Eq_refl;
Save orelse_true;

(* deMorgan laws *)
Goal deMorgan : {a,b:bool}iff (is_false (orelse a b)) (and (is_false a) (is_false b));
intros; Refine pair;
intros hyp; Refine pair;
Refine true_or_false a; intros truea; Refine true_not_false;
Qrepl Eq_sym hyp; Qrepl truea; Refine Eq_refl;
intros; Immed;
Refine true_or_false b; intros trueb; Refine true_not_false;
Qrepl Eq_sym hyp; Qrepl orelse_commutes a b; Qrepl trueb; Refine Eq_refl;
intros; Immed;
intros g; Qrepl fst g; Qrepl snd g; Refine Eq_refl;
Save deMorgan;

Goal {a,b:bool}  (is_false (a .andalso b)) .iff ((is_false a ) \/ (is_false b));
Refine bool_double_elim [a,b:bool]  (is_false (a .andalso b)) .iff ((is_false a ) \/ (is_false b));
andI;
intros;
Refine true_not_false H;
intros;
Refine H;
Refine ? +1;
intros;
Refine true_not_false H1;
andI;
intros;
Refine inr;
Refine Eq_refl;
intros;
Refine Eq_refl;
andI;
intros;
Refine inl;
Refine Eq_refl;
intros;
Refine Eq_refl;
andI;
intros;
Refine inr;
Refine Eq_refl;
intros;
Refine Eq_refl;
Save deMorgan';

(* implies *)
Goal implies_character : {a,b:bool}iff (is_true (implies a b)) ((is_true a)->(is_true b));
intros; 
Refine pair;
intros;
Refine Eq_subst H;
Qrepl H1;
Refine true_or_false b; 
intros; 
Qrepl H2;
Refine Eq_refl;
intros; 
Qrepl H2;
Refine Eq_refl;
intros;
Refine true_or_false a; 
intros; 
Qrepl H H1;
Refine Eq_refl;
intros; 
Qrepl H1;
Refine if_absorbs;
Save implies_character;
 
Goal implies_false : {n:bool} is_true (implies false n);
Refine bool_ind [n:bool]is_true (implies false n);
Refine Eq_refl; Refine Eq_refl;
Save implies_false;
