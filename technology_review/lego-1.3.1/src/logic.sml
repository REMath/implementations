(* logic.sml *)

val logicPreludeXCC = "\
\(* logic.ml *)  (** Logical Preliminaries **)\
\\
\[A,B,C,D|Prop][a:A][b:B][c:C][d:D][T,S,U|Type]\
\\
\(* cut *)\
\[cut = [a:A][h:A->B]h a : A->(A->B)->B]\
\\
\(* Some Combinators *)\
\[I [t:T] = t : T]\
\[compose [f:S->U][g:T->S] = [x:T]f (g x) : T->U]\
\[permute [f:T->S->U] = [s:S][t:T]f t s : S->T->U];\
\DischargeKeep A;\
\\
\(* Conjunction, Disjunction and Negation *)\
\[and [A,B:Prop] = {C|Prop}(A->B->C)->C : Prop]\
\[or  [A,B:Prop] = {C|Prop}(A->C)->(B->C)->C : Prop]\
\(* Introduction Rules *)\
\[pair = [C|Prop][h:A->B->C](h a b) : and A B]\
\[inl = [C|Prop][h:A->C][_:B->C]h a : or A B]\
\[inr = [C|Prop][_:A->C][h:B->C]h b : or A B]\
\(* Elimination Rules - 'and' & 'or' are their own elim rules *)\
\[fst [h:and A B] = h [g:A][_:B]g : A]\
\[snd [h:and A B] = h [_:A][g:B]g : B]\
\\
\(* Logical Equivalence *)\
\[iff [A,B:Prop] = and (A->B) (B->A) : Prop]\
\\
\(* Negation *)\
\[absurd = {A:Prop}A]\
\[not [A:Prop] = A->absurd]\
\\
\(* Quantification *)\
\(* a uniform Pi *)\
\[All [P:T->Prop] = {x:T}P x : Prop]\
\(* Existential quantifier *)\
\[Ex [P:T->Prop] = {B:Prop}({t:T}(P t)->B)->B : Prop]\
\[ExIntro [P:T->Prop][wit|T][prf:P wit]\
\ = [B:Prop][gen:{t:T}(P t)->B](gen wit prf) : Ex P]\
\(* Existential restricted to Prop has a witness *)\
\[ex [P:A->Prop] = {B:Prop}({a:A}(P a)->B)->B : Prop]\
\[ex_intro [P:A->Prop][wit|A][prf:P wit]\
\ = [B:Prop][gen:{a:A}(P a)->B](gen wit prf) : ex P]\
\[witness [P|A->Prop][p:ex P] = p A [x:A][y:P x]x : A]\
\\
\(* tuples *)\
\[and3 [A,B,C:Prop] = {X|Prop}(A->B->C->X)->X : Prop]\
\[pair3 = [X|Prop][h:A->B->C->X]h a b c : and3 A B C]\
\[and3_out1 [p:and3 A B C] = p [a:A][_:B][_:C]a : A]\
\[and3_out2 [p:and3 A B C] = p [_:A][b:B][_:C]b : B]\
\[and3_out3 [p:and3 A B C] = p [_:A][_:B][c:C]c : C]\
\[iff3 [A,B,C:Prop] = and3 (A->B) (B->C) (C->A) : Prop]\
\\
\(* finite sums *)\
\[or3 [A,B,C:Prop] = {X|Prop}(A->X)->(B->X)->(C->X)->X : Prop]\
\[or3_in1 = [X|Prop][h:A->X][_:B->X][_:C->X](h a) : or3 A B C]\
\[or3_in2 = [X|Prop][_:A->X][h:B->X][_:C->X](h b) : or3 A B C]\
\[or3_in3 = [X|Prop][_:A->X][_:B->X][h:C->X](h c) : or3 A B C]\
\\
\(* Relations *)\
\[R:T->T->Prop]\
\[refl = {t:T}R t t : Prop]\
\[sym = {t,u|T}(R t u)->(R u t) : Prop]\
\[trans = {t,u,v|T}(R t u)->(R u v)->(R t v) : Prop];\
\Discharge R;\
\(* families of relations *)\
\[respect [f:T->S][R:{X|Type}X->X->Prop]\
\  = {t,u|T}(R t u)->(R (f t) (f u)) : Prop];\
\DischargeKeep A;\
\\
\(* Equality *)\
\[Q [x,y:T] = {P:T->Prop}(P x)->(P y) : Prop]\
\[Q_refl = [t:T][P:T->Prop][h:P t]h : refl Q]\
\[Q_sym = [t,u|T][g:Q t u]g ([x:T]Q x t) (Q_refl t) : sym Q]\
\[Q_trans : trans Q\
\  = [t,u,v|T][p:Q t u][q:Q u v][P:T->Prop]compose (q P) (p P)];\
\DischargeKeep A;\
\(* application respects equality; a substitution property *)\
\[Q_resp [f:T->S] : respect f Q\
\  = [t,u|T][h:Q t u]h ([z:T]Q (f t) (f z)) (Q_refl (f t))];\
\Discharge A;";


val logicPreludePCC = "\
\(* logic.ml *)  (** Logical Preliminaries **)\
\\
\[A,B,C,D|Prop][a:A][b:B][c:C][d:D][T,S,U|Prop]\
\\
\(* cut *)\
\[cut = [a:A][h:A->B]h a : A->(A->B)->B]\
\\
\(* Some Combinators *)\
\[I [t:T] = t : T]\
\[compose [f:S->U][g:T->S] = [x:T]f (g x) : T->U]\
\[permute [f:T->S->U] = [s:S][t:T]f t s : S->T->U];\
\DischargeKeep A;\
\\
\(* Conjunction, Disjunction and Negation *)\
\[and [A,B:Prop] = {C|Prop}(A->B->C)->C : Prop]\
\[or  [A,B:Prop] = {C|Prop}(A->C)->(B->C)->C : Prop]\
\(* Introduction Rules *)\
\[pair = [C|Prop][h:A->B->C](h a b) : and A B]\
\[inl = [C|Prop][h:A->C][_:B->C]h a : or A B]\
\[inr = [C|Prop][_:A->C][h:B->C]h b : or A B]\
\(* Elimination Rules - 'and' & 'or' are their own elim rules *)\
\[fst [h:and A B] = h [g:A][_:B]g : A]\
\[snd [h:and A B] = h [_:A][g:B]g : B]\
\\
\(* Logical Equivalence *)\
\[iff [A,B:Prop] = and (A->B) (B->A) : Prop]\
\\
\(* Negation *)\
\[absurd = {A:Prop}A]\
\[not [A:Prop] = A->absurd]\
\\
\(* Quantification *)\
\(* a uniform Pi *)\
\[All [P:T->Prop] = {x:T}P x : Prop]\
\(* Existential quantifier *)\
\[Ex [P:T->Prop] = {B:Prop}({t:T}(P t)->B)->B : Prop]\
\[ExIntro [P:T->Prop][wit|T][prf:P wit]\
\ = [B:Prop][gen:{t:T}(P t)->B](gen wit prf) : Ex P]\
\(* Existential restricted to Prop has a witness *)\
\[ex [P:A->Prop] = {B:Prop}({a:A}(P a)->B)->B : Prop]\
\[ex_intro [P:A->Prop][wit|A][prf:P wit]\
\ = [B:Prop][gen:{a:A}(P a)->B](gen wit prf) : ex P]\
\[witness [P|A->Prop][p:ex P] = p A [x:A][y:P x]x : A]\
\\
\(* tuples *)\
\[and3 [A,B,C:Prop] = {X|Prop}(A->B->C->X)->X : Prop]\
\[pair3 = [X|Prop][h:A->B->C->X]h a b c : and3 A B C]\
\[and3_out1 [p:and3 A B C] = p [a:A][_:B][_:C]a : A]\
\[and3_out2 [p:and3 A B C] = p [_:A][b:B][_:C]b : B]\
\[and3_out3 [p:and3 A B C] = p [_:A][_:B][c:C]c : C]\
\[iff3 [A,B,C:Prop] = and3 (A->B) (B->C) (C->A) : Prop]\
\\
\(* finite sums *)\
\[or3 [A,B,C:Prop] = {X|Prop}(A->X)->(B->X)->(C->X)->X : Prop]\
\[or3_in1 = [X|Prop][h:A->X][_:B->X][_:C->X](h a) : or3 A B C]\
\[or3_in2 = [X|Prop][_:A->X][h:B->X][_:C->X](h b) : or3 A B C]\
\[or3_in3 = [X|Prop][_:A->X][_:B->X][h:C->X](h c) : or3 A B C]\
\\
\(* Relations *)\
\[R:T->T->Prop]\
\[refl = {t:T}R t t : Prop]\
\[sym = {t,u|T}(R t u)->(R u t) : Prop]\
\[trans = {t,u,v|T}(R t u)->(R u v)->(R t v) : Prop];\
\Discharge R;\
\(* families of relations *)\
\[respect [f:T->S][R:{X|Prop}X->X->Prop]\
\  = {t,u|T}(R t u)->(R (f t) (f u)) : Prop];\
\DischargeKeep A;\
\\
\(* Equality *)\
\[Q [x,y:T] = {P:T->Prop}(P x)->(P y) : Prop]\
\[Q_refl = [t:T][P:T->Prop][h:P t]h : refl Q]\
\[Q_sym = [t,u|T][g:Q t u]g ([x:T]Q x t) (Q_refl t) : sym Q]\
\[Q_trans : trans Q\
\  = [t,u,v|T][p:Q t u][q:Q u v][P:T->Prop]compose (q P) (p P)];\
\DischargeKeep A;\
\(* application respects equality; a substitution property *)\
\[Q_resp [f:T->S] : respect f Q\
\  = [t,u|T][h:Q t u]h ([z:T]Q (f t) (f z)) (Q_refl (f t))];\
\Discharge A;";
