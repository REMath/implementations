Module lib_logic Import parameters;

(* Contents
   --------
   o Impredicative encodings of and, or, Ex, etc. and their introduction and 
     elimination rules.  

   o Definitions of some properties of relations.

   17 Nov 1996 Thomas Schreiber <tms@dcs.ed.ac.uk>
               added forall_elim and impl_elim for proof-by-pointing
               algorithm
*)

Configure Infix /\ left 3;
Configure Infix \/ left 2;

[A,B,C,D,E,F,G|Prop] 

[a:A][b:B][c:C][d:D][e:E][f:F][g:G];

[T,S,U,V,W,X|SET];


[     cut = [a:A][h:A->B]h a
          : A->(A->B)->B
]
[     trueProp = {P:Prop}P->P
          : Prop
]
[     Id = [t:T]t
          : T->T
]
[     PropId = [a:A]a
          : A->A 
]
[     Contrapos = [H:A->B][X|Prop][H1:B->X][H2:A]H1 (H H2)
          : (A->B)->{X|Prop}(B->X)->A->X
]
[     compose = [f:S->U][g:T->S][x:T]f (g x)
          : (S->U)->(T->S)->T->U
]
[     permute = [f:T->S->U][s:S][t:T]f t s
          : (T->S->U)->S->T->U
]
[     forall_elim = [P:T->Prop][H:{x:T}P x][e:T][pc:(P e)->C]pc (H e)
          : {P:T->Prop}({x:T}P x)->{e:T}((P e)->C)->C
]
[     impl_elim = [ab:A->B][a:A][bc:B->C]bc (ab a)
          : (A->B)->A->(B->C)->C
];

DischargeKeep A;

[     and = [A,B:Prop]{C|Prop}(A->B->C)->C
          : Prop->Prop->Prop
]
[     or = [A,B:Prop]{C|Prop}(A->C)->(B->C)->C
          : Prop->Prop->Prop 
]
[     or_elim = [M:or A B][N1:A->C][N2:B->C]M N1 N2
          : (or A B)->(A->C)->(B->C)->C
]
[     pair = [C|Prop][h:A->B->C]h a b
          : and A B 
]
[     inl = [C|Prop][h:A->C][_:B->C]h a
          : or A B 
]
[     inr = [C|Prop][_:A->C][h:B->C]h b   
          : or A B 
]
[     fst = [h:and A B]h ([g:A][_:B]g)
          : (and A B)->A 
]
[     snd = [h:and A B]h ([_:A][g:B]g)
          : (and A B)->B 
]
[     iff = [A,B:Prop]and (A->B) (B->A)
          : Prop->Prop->Prop
]
[     absurd = {A:Prop}A
          : Prop 
]
[     absurd_elim = [M:absurd][N:Prop]M N
          : absurd->{N:Prop}N
]
[     not = [A:Prop]A->absurd
          : Prop->Prop 
]
[     All = [P:T->Prop]{x:T}P x
          : (T->Prop)->Prop 
]
[     Ex = [P:T->Prop]{B:Prop}({t:T}(P t)->B)->B
          : (T->Prop)->Prop
]
[     ExIntro = [wit:T][P:T->Prop][prf:P wit][B:Prop][gen:{t:T}
                  (P t)->B]gen wit prf
          : {wit:T}{P:T->Prop}(P wit)->Ex P 
]
[     ExIn = [wit:T][P:T->Prop][prf:P wit][B:Prop]
             [gen:{t:T}(P t)->B]gen wit prf
]
[     ExElim = [P|T->Prop][M:Ex P][N|Prop][prf:{t:T}(P t)->N]M N prf
          : {P|T->Prop}(Ex P)->{N|Prop}({t:T}(P t)->N)->N
]
[     ex = [P:A->Prop]{B:Prop}({a:A}(P a)->B)->B
          : (A->Prop)->Prop 
]
[     ex_intro = [P:A->Prop][wit|A][prf:P wit][B:Prop][gen:{a:A}(P a)->B]
                   gen wit prf
          : {P:A->Prop}{wit|A}(P wit)->ex P 
]
[     witness = [P|A->Prop][p:ex P]p A ([x:A][_:P x]x)
          : {P|A->Prop}(ex P)->A 
] 
[     Ex2 = [P:T->S->Prop]{B:Prop}({t|T}{s|S}(P t s)->B)->B
          : (T->S->Prop)->Prop 
]
[     Ex2Intro [P:T->S->Prop][t|T][s|S][p:P t s] = [B:Prop][gen:{t|T}{s|S}
                 (P t s)->B]gen p
          : Ex2 P 
]
[Ex2Elim = [P|T->S->Prop][M:Ex2 P][N|Prop][prf:{t|T}{s|S}(P t s)->N]M N prf
          : {P|T->S->Prop}(Ex2 P)->{N|Prop}({t|T}{s|S}(P t s)->N)->N]
[Ex2In [t:T][s:S][P:T->S->Prop][p:P t s] : Ex2 P =
    [B:Prop][gen:{t|T}{s|S}(P t s)->B]gen p];
[Ex3 [P:T->S->U->Prop] : Prop =
    {B:Prop}({t|T}{s|S}{u|U}(P t s u)->B)->B];
[Ex3In [t:T][s:S][u:U][P:T->S->U->Prop][p:P t s u] : Ex3 P =
    [B:Prop][gen:{t|T}{s|S}{u|U}(P t s u)->B]gen p];
[Ex3Elim = [P|T->S->U->Prop][M:Ex3 P][N|Prop]
           [prf:{t|T}{s|S}{u|U}(P t s u)->N]M N prf
          : {P|T->S->U->Prop}(Ex3 P)->{N|Prop}({t|T}{s|S}{u|U}(P t s u)->N)->N]
[Ex4 [P:T->S->U->V->Prop] : Prop =
    {B:Prop}({t|T}{s|S}{u|U}{v|V}(P t s u v)->B)->B];
[Ex4In [t:T][s:S][u:U][v:V][P:T->S->U->V->Prop][p:P t s u v] : Ex4 P =
    [B:Prop][gen:{t|T}{s|S}{u|U}{v|V}(P t s u v)->B]gen p];
[Ex4Elim = [P|T->S->U->V->Prop][M:Ex4 P][N|Prop]
           [prf:{t|T}{s|S}{u|U}{v|V}(P t s u v)->N]M N prf
          : {P|T->S->U->V->Prop}(Ex4 P)->
	    {N|Prop}({t|T}{s|S}{u|U}{v|V}(P t s u v)->N)->N]
[Ex5 [P:T->S->U->V->W->Prop] : Prop =
    {B:Prop}({t|T}{s|S}{u|U}{v|V}{w|W}(P t s u v w)->B)->B];
[Ex5In [t:T][s:S][u:U][v:V][w:W][P:T->S->U->V->W->Prop][p:P t s u v w] : Ex5 P =
    [B:Prop][gen:{t|T}{s|S}{u|U}{v|V}{w|W}(P t s u v w)->B]gen p];
[Ex5Elim = [P|T->S->U->V->W->Prop][M:Ex5 P][N|Prop]
           [prf:{t|T}{s|S}{u|U}{v|V}{w|W}(P t s u v w)->N]M N prf
          : {P|T->S->U->V->W->Prop}(Ex5 P)->
	    {N|Prop}({t|T}{s|S}{u|U}{v|V}{w|W}(P t s u v w)->N)->N]
[Ex6 [P:T->S->U->V->W->X->Prop] : Prop =
    {B:Prop}({t|T}{s|S}{u|U}{v|V}{w|W}{x|X}(P t s u v w x)->B)->B];
[Ex6In [t:T][s:S][u:U][v:V][w:W][x:X][P:T->S->U->V->W->X->Prop][p:P t s u v w x]
      : Ex6 P
      = [B:Prop][gen:{t|T}{s|S}{u|U}{v|V}{w|W}{x|X}(P t s u v w x)->B]gen p];
[Ex6Elim = [P|T->S->U->V->W->X->Prop][M:Ex6 P][N|Prop]
           [prf:{t|T}{s|S}{u|U}{v|V}{w|W}{x|X}(P t s u v w x)->N]M N prf
          : {P|T->S->U->V->W->X->Prop}(Ex6 P)->
	    {N|Prop}({t|T}{s|S}{u|U}{v|V}{w|W}{x|X}(P t s u v w x)->N)->N]
[     and3 = [A,B,C:Prop]{X|Prop}(A->B->C->X)->X
          : Prop->Prop->Prop->Prop 
]
[     pair3 = [X|Prop][h:A->B->C->X]h a b c
          : and3 A B C 
]
[     and3_out1 = [p:and3 A B C]p ([a:A][_:B][_:C]a)
          : (and3 A B C)->A 
]
[     and3_out2 = [p:and3 A B C]p ([_:A][b:B][_:C]b)
          : (and3 A B C)->B 
]
[     and3_out3 = [p:and3 A B C]p ([_:A][_:B][c:C]c)
          : (and3 A B C)->C 
]
[and4 [A,B,C,D:Prop] = {chi|Prop}{premise:A->B->C->D->chi}chi];
[pair4 = [chi|Prop][premise:A->B->C->D->chi](premise a b c d):and4 A B C D];
[and4_out1 [conj:and4 A B C D] = conj|A [a:A][_:B][_:C][_:D]a:A];
[and4_out2 [conj:and4 A B C D] = conj|B [_:A][b:B][_:C][_:D]b:B];
[and4_out3 [conj:and4 A B C D] = conj|C [_:A][_:B][c:C][_:D]c:C];
[and4_out4 [conj:and4 A B C D] = conj|D [_:A][_:B][_:C][d:D]d:D];

[and5 [A,B,C,D,E:Prop] = {chi|Prop}{premise:A->B->C->D->E->chi}chi];
[pair5 = [chi|Prop][premise:A->B->C->D->E->chi](premise a b c d e):and5 A B C D E];
[and5_out1 [conj:and5 A B C D E] = conj|A [a:A][_:B][_:C][_:D][_:E]a:A];
[and5_out2 [conj:and5 A B C D E] = conj|B [_:A][b:B][_:C][_:D][_:E]b:B];
[and5_out3 [conj:and5 A B C D E] = conj|C [_:A][_:B][c:C][_:D][_:E]c:C];
[and5_out4 [conj:and5 A B C D E] = conj|D [_:A][_:B][_:C][d:D][_:E]d:D];
[and5_out5 [conj:and5 A B C D E] = conj|E [_:A][_:B][_:C][_:D][e:E]e:E];

[and6 [A,B,C,D,E,F:Prop] = {chi|Prop}{premise:A->B->C->D->E->F->chi}chi];
[pair6 = [chi|Prop][premise:A->B->C->D->E->F->chi](premise a b c d e f)
       : and6 A B C D E F];
[and6_out1 [conj:and6 A B C D E F] = conj|A [a:A][_:B][_:C][_:D][_:E][_:F]a:A];
[and6_out2 [conj:and6 A B C D E F] = conj|B [_:A][b:B][_:C][_:D][_:E][_:F]b:B];
[and6_out3 [conj:and6 A B C D E F] = conj|C [_:A][_:B][c:C][_:D][_:E][_:F]c:C];
[and6_out4 [conj:and6 A B C D E F] = conj|D [_:A][_:B][_:C][d:D][_:E][_:F]d:D];
[and6_out5 [conj:and6 A B C D E F] = conj|E [_:A][_:B][_:C][_:D][e:E][_:F]e:E];
[and6_out6 [conj:and6 A B C D E F] = conj|F [_:A][_:B][_:C][_:D][_:E][f:F]f:F];

[and7 [A,B,C,D,E,F,G:Prop] = {chi|Prop}{premise:A->B->C->D->E->F->G->chi}chi];
[pair7 = [chi|Prop][premise:A->B->C->D->E->F->G->chi](premise a b c d e f g)
       : and7 A B C D E F G];
[and7_out1 [conj:and7 A B C D E F G] = conj|A [a:A][_:B][_:C][_:D][_:E][_:F][_:G]a:A];
[and7_out2 [conj:and7 A B C D E F G] = conj|B [_:A][b:B][_:C][_:D][_:E][_:F][_:G]b:B];
[and7_out3 [conj:and7 A B C D E F G] = conj|C [_:A][_:B][c:C][_:D][_:E][_:F][_:G]c:C];
[and7_out4 [conj:and7 A B C D E F G] = conj|D [_:A][_:B][_:C][d:D][_:E][_:F][_:G]d:D];
[and7_out5 [conj:and7 A B C D E F G] = conj|E [_:A][_:B][_:C][_:D][e:E][_:F][_:G]e:E];
[and7_out6 [conj:and7 A B C D E F G] = conj|F [_:A][_:B][_:C][_:D][_:E][f:F][_:G]f:F];
[and7_out7 [conj:and7 A B C D E F G] = conj|G [_:A][_:B][_:C][_:D][_:E][_:F][g:G]g:G];

[     iff3 = [A,B,C:Prop]and3 (A->B) (B->C) (C->A)
          : Prop->Prop->Prop->Prop 
]
[     or3 = [A,B,C:Prop]{X|Prop}(A->X)->(B->X)->(C->X)->X
          : Prop->Prop->Prop->Prop 
]
[     or3_in1 = [X|Prop][h:A->X][_:B->X][_:C->X]h a
          : or3 A B C 
]
[     or3_in2 = [X|Prop][_:A->X][h:B->X][_:C->X]h b
          : or3 A B C 
]
[     or3_in3 = [X|Prop][_:A->X][_:B->X][h:C->X]h c
          : or3 A B C 
]
[     or3_elim = [X|Prop][M:or3 A B C][N1:A->X][N2:B->X][N3:C->X]M N1 N2 N3
          : {X|Prop}(or3 A B C)->(A->X)->(B->X)->(C->X)->X
];

[R:T->T->Prop];

[     refl = {t:T}R t t
          : Prop 
]
[     sym = {t,u|T}(R t u)->R u t
          : Prop 
]
[     trans = {t,u,v|T}(R t u)->(R u v)->R t v
          : Prop 
];

[Equivalence = and3 refl sym trans];



Discharge R;

[     respect = [f:T->S][R:{X|SET}X->X->Prop]{t,u|T}(R t u)->R (f t) (f u)
          : (T->S)->({X|SET}X->X->Prop)->Prop 
]
[     respect2 = [f:T->U->S][R:{X|SET}X->X->Prop]
                    {t,t':T}{u,u':U}(R t t')->(R u u')->R (f t u) (f t' u')
          : (T->U->S)->({X|SET}X->X->Prop)->Prop 
];

Discharge A;

