
(* ~jhm/Lego/relations.l January/August 1991. Beginning again *)

(* CHANGES

   24 Jan 1996
   Thomas Schreiber <tms@dcs.ed.ac.uk>
   converted LEGO file to library compatible module for arbitrary equality

   30 Jan 1997
   Thomas Schreiber <tms@dcs.ed.ac.uk>
   added definition for well-foundedness
   *)

Module lib_rel Import lib_nat;

[Pred = [s:Type]s->Prop];
[Rel = [s,t:Type]s->t->Prop];



[s,t,u,v|Type];

[preserves [f:s->t][R:Rel s s][Q:Rel t t]
   = {t,u|s}(R t u)->Q (f t) (f u)];
[R:Rel s s]

[WF  = {P:s->Prop}
       {wh_ih:{n:s}({x:s}(R x n)->P x)->P n}
       {m:s}P m]
[TWF = and (trans R) WF];
[per = and (sym R) (trans R)];
[equiv = and (refl R) per ];
[preorder = and (refl R) (trans R)];
[PreorderEq [preR:preorder] = [x,y:s]and(R x y)(R y x):Rel s s];
Discharge R; DischargeKeep s;

[SubPred = [F,G:Pred s]{x|s}{hyp:F x}G x];
[reflSubPred = [F:Pred s][x|s][hyp:F x]hyp:refl SubPred];
[transSubPred = [F,G,H|Pred s][FsubG:SubPred F G][GsubH:SubPred G H]
                [x|s][hyp:F x]GsubH (FsubG hyp):trans SubPred];
[EqPred = PreorderEq SubPred (pair reflSubPred transSubPred)]
(*[F,G:Pred s]and (SubPred F G) (SubPred G F):Rel (Pred s) (Pred s)]*);
[SubRel = [Q,R:Rel s t]{x|s}{y|t}{hyp:Q x y}R x y];
[reflSubRel = [P:Rel s t][x|s][y|t][hyp:P x y]hyp:refl SubRel];
[transSubRel = [P,Q,R|Rel s t][PsubQ:SubRel P Q][QsubR:SubRel Q R]
               [x|s][y|t][hyp:P x y]QsubR (PsubQ hyp):trans SubRel];
[EqRel = PreorderEq SubRel (pair reflSubRel transSubRel)]
(*[Q,R:Rel s t]and (SubRel Q R) (SubRel R Q):Rel (Rel s t) (Rel s t)]*);
DischargeKeep s;

[E,F,G|Pred s][H|Pred t][f|t -> s];

[andPred [F,G:Pred s] = [x:s]and (F x) (G x):Pred s];
[orPred [F,G:Pred s] = [x:s]or (F x) (G x):Pred s];
[impliesPred [G,E:Pred s] = [x:s]{hypG:G x}E x:Pred s];
[notPred [F:Pred s] = [x:s]not(F x):Pred s];

Goal andPredI : (SubPred E F) -> (SubPred E G) -> SubPred E (andPred F G);
Intros EsubF EsubG __;Refine pair;Refine EsubF;Refine +1 EsubG;Immed;
Save andPredI;

Goal andPredE1 : (SubPred E (andPred F G)) -> (SubPred E F);
Intros EsubFandG __;Refine fst (EsubFandG hyp);
Save andPredE1;

Goal andPredE2 : (SubPred E (andPred F G)) -> (SubPred E G);
Intros EsubFandG __;Refine snd (EsubFandG hyp);
Save andPredE2;

Goal orPredE : (SubPred F E) ->  (SubPred G E) -> SubPred (orPred F G) E;
Intros FsubE GsubE __;Refine hyp;Immed;
Save orPredE;

Goal orPredI1 : (SubPred E F) -> SubPred E (orPred F G); 
Intros EsubF __;Refine inl;Refine EsubF;Immed;
Save orPredI1;

Goal orPredI2 : (SubPred E G) -> SubPred E (orPred F G); 
Intros EsubF __;Refine inr;Refine EsubF;Immed;
Save orPredI2;

Goal impliesPredI : (SubPred (andPred F G) E) -> SubPred F (impliesPred G E);
Intros FandGsubE ___;Refine FandGsubE;Refine pair;Immed;
Save impliesPredI;

Goal impliesPredE : (SubPred F (impliesPred G E)) -> SubPred (andPred F G) E;
Intros FsubGimpE __;Refine hyp;Refine FsubGimpE;
Save impliesPredE;

[existsf [f:t -> s][H:Pred t] = [x:s]
   {phi:Prop}{ex_y:{y:t}{eq:Eq (f y) x}{hypH:H y}phi}phi:Pred s];
[starf [f:t -> s][F:Pred s]   = [y:t]F (f y):Pred t];
[forallf [f:t -> s][H:Pred t] = [x:s]{y:t}{eq:Eq x (f y)}H y:Pred s];

Goal existsfE : (SubPred (existsf f H) F) -> SubPred H (starf f F);
Intros exfHsubF __;Refine exfHsubF;Intros;Refine ex_y;Refine +1 Eq_refl;Immed;
Save existsfE;
Goal existsfI : (SubPred H (starf f F)) -> SubPred (existsf f H) F;
Intros HsubfF __;Refine hyp;intros;
Qrepl Eq_sym eq; Refine HsubfF;Immed;
Save existsfI;
Goal forallfE : (SubPred F (forallf f H)) -> SubPred (starf f F) H;
Intros FsuballfH __;Refine FsuballfH;Refine +2 Eq_refl;Immed;
Save forallfE;
Goal forallfI : (SubPred (starf f F) H) -> SubPred F (forallf f H);
Intros fFsubH ____;Refine fFsubH; Expand starf; Qrepl Eq_sym eq;Immed;
Save forallfI;

[P,Q,R|Rel s t][S|Rel t u][T|Rel s u][U|Rel u v][g|u -> v -> s][h|u -> v -> t];

[op [P:Rel s t] = [y:t][x:s]P x y:Rel t s];
[notRel [P:Rel s t] = [x:s][y:t]not(P x y):Rel s t];
[andRel [P,Q:Rel s t] = [x:s][y:t]and (P x y) (Q x y):Rel s t];
[orRel [P,Q:Rel s t] = [x:s][y:t]or (P x y) (Q x y):Rel s t];
[composeRel [R:Rel s t][S:Rel t u] = [x:s][z:u]
   {phi:Prop}{ex_y:{y:t}{hypR:R x y}{hypS:S y z}phi}phi:Rel s u];
[impliesRel [R:Rel s t][T:Rel s u] = [y:t][z:u]{x:s}{hypR:R x y}T x z:Rel t u];
[coimpliesRel [S:Rel t u][T:Rel s u] = [x:s][y:t]{z:u}{hypS:S y z}T x z:Rel s t];

Goal andRelI : (SubRel R P) -> (SubRel R Q) -> SubRel R (andRel P Q);
Intros RsubP RsubQ ___;Refine pair;Refine RsubP;Refine +1 RsubQ;Immed;
Save andRelI;

Goal andRelE1 : (SubRel R (andRel P Q)) -> (SubRel R P);
Intros RsubPandQ ___;Refine fst (RsubPandQ hyp);
Save andRelE1;

Goal andRelE2 : (SubRel R (andRel P Q)) -> (SubRel R Q);
Intros RsubPandQ ___;Refine snd (RsubPandQ hyp);
Save andRelE2;

Goal orRelE : (SubRel P R) ->  (SubRel Q R) -> SubRel (orRel P Q) R;
Intros PsubR QsubR ___;Refine hyp;Immed;
Save orRelE;

Goal orRelI1 : (SubRel R P) -> SubRel R (orRel P Q); 
Intros RsubP ___;Refine inl;Refine RsubP;Immed;
Save orRelI1;

Goal orRelI2 : (SubRel R Q) -> SubRel R (orRel P Q); 
Intros RsubP ___;Refine inr;Refine RsubP;Immed;
Save orRelI2;

Goal impliesRelI : (SubRel (composeRel R S) T)-> SubRel S (impliesRel R T);
Intros  RdotSsubT y w ___;Refine RdotSsubT;Intros;Refine ex_y;Immed;
Save impliesRelI;

Goal impliesRelE : (SubRel S (impliesRel R T)) -> SubRel (composeRel R S) T;
Intros RsubSimpT x z _;Refine hyp;intros;Refine RsubSimpT;Immed;
Save impliesRelE;

Goal coimpliesRelI : (SubRel (composeRel R S) T)-> SubRel R (coimpliesRel S T);
Intros RdotSsubT x y ___;Refine RdotSsubT;Intros;Refine ex_y;Immed;
Save coimpliesRelI;

Goal coimpliesRelE : (SubRel R (coimpliesRel S T)) -> SubRel (composeRel R S) T;
Intros RsubScoimpT x z _;Refine hyp;intros;Refine RsubScoimpT;Immed;
Save coimpliesRelE;

[existsgh [g:u->v->s][h:u->v->t][U:Rel u v] = [x:s][y:t]{phi:Prop}
{ex_zw:{z:u}{w:v}{eqg:Eq (g z w) x}{eqh:Eq (h z w) y}{hypU:U z w}phi}phi:Rel s t];
[stargh [g:u->v->s][h:u->v->t][P:Rel s t] = [z:u][w:v]P (g z w) (h z w):Rel u v];
[forallgh [g:u -> v -> s][h:u -> v -> t][U:Rel u v] = [x:s][y:t]
          {z:u}{w:v}{eqg:Eq x (g z w)}{eqh:Eq y (h z w)}U z w:Rel s t];

Goal existsghE : (SubRel (existsgh g h U) P) -> SubRel U (stargh g h P);
Intros exghUsubP z w _;Refine exghUsubP;Intros;Refine ex_zw; 
Refine +2 Eq_refl;Refine Eq_refl;Immed;
Save existsghE;
Goal existsghI : (SubRel U (stargh g h P)) -> SubRel (existsgh g h U) P;
Intros UsubghP ___;Refine hyp;
intros; Qrepl Eq_sym eqh; Qrepl Eq_sym eqg;
Refine UsubghP;Immed;
Save existsghI;
Goal forallghE : (SubRel P (forallgh g h U)) -> SubRel (stargh g h P) U;
Intros PsuballghU z w _;Refine PsuballghU;Refine +3 Eq_refl;Refine +2 Eq_refl;Immed;
Save forallghE;
Goal forallghI : (SubRel (stargh g h P) U) -> SubRel P (forallgh g h U);
Intros ghPsubU _______;Refine ghPsubU; Expand stargh;
Qrepl Eq_sym eqh; Qrepl Eq_sym eqg;Immed;
Save forallghI;

[KPred [P:Prop] = [x:s]P:Pred s];
[KRelL [F:Pred s] = [x:s][y:t]F x:Rel s t];
[KRelR [G:Pred t] = [x:s][y:t]G y:Rel s t];

[leftKanPred [R:Rel s t][F:Pred s] = [y:t]
             {phi:Prop}{ex_x:{x:s}{hypR:R x y}{hypF:F x}phi}phi:Pred t];
[rightKanPred [R:Rel s t][F:Pred s] = [y:t]{x:s}{hypR:R x y}F x:Pred t];

Goal notPredIE : {EsubF:SubPred E F}SubPred (notPred F) (notPred E);
Intros;Refine hyp;Refine EsubF;Immed;
Save notPredIE;

Goal notRelIE : {PsubQ:SubRel P Q}SubRel (notRel Q) (notRel P);
Intros;Refine hyp;Refine PsubQ;Immed;
Save notRelIE;

[univPred = KPred trueProp];
[univRel = KRelL univPred];
[emptyPred = KPred absurd];
[emptyRel = KRelL emptyPred];

Goal univPredI : SubPred F univPred;
Intros;Immed;
Save univPredI;

Goal emptyPredI : SubPred emptyPred F;
Intros;Refine hyp;
Save emptyPredI;

Goal univRelI : SubRel R univRel;
Intros;Immed;
Save univRelI;

Goal emptyRelI : SubRel emptyRel R;
Intros;Refine hyp;
Save emptyRelI;

DischargeKeep E;

Goal existfunit : SubPred H (starf f (existsf f H));
Refine existsfE;Refine reflSubPred;
Save existfunit;
Goal existfcounit : SubPred (existsf f (starf f F)) F;
Refine existsfI;Refine reflSubPred;
Save existfcounit;
Goal forallfunit : SubPred F (forallf f (starf f F)); 
Refine forallfI;Refine reflSubPred;
Save forallfunit;
Goal forallfcounit : SubPred (starf f (forallf f H)) H; 
Refine forallfE;Refine reflSubPred;
Save forallfcounit;

Goal existghunit : SubRel U (stargh g h (existsgh g h U));
Refine existsghE;Refine reflSubRel;
Save existghunit;
Goal existghcounit : SubRel (existsgh g h (stargh g h P)) P;
Refine existsghI;Refine reflSubRel;
Save existghcounit;
Goal forallghunit : SubRel P (forallgh g h (stargh g h P)); 
Refine forallghI;Refine reflSubRel;
Save forallghunit;
Goal forallghcounit : SubRel (stargh g h (forallgh g h U)) U; 
Refine forallghE;Refine reflSubRel;
Save forallghcounit;

[monotonePred [phi:(Pred s) -> Pred t] = preserves phi (SubPred|s) (SubPred|t)];
[monotoneRel [phi:(Rel s t) -> Rel u v] = preserves phi (SubRel|s|t)(SubRel|u|v)];

DischargeKeep s;

Goal opMono : {PsubQ:SubRel P Q}SubRel (op P) (op Q);
Intros;Refine PsubQ;Immed;
Save opMono;

Goal opInvol : SubRel P (op (op P));
Intros;Immed;
Save opInvol;

Discharge E;

[P|Rel s t][Q|Rel t u][R|Rel u v];(* have these all as "EqRel"s??? *)

Goal composeRelMonoL : monotoneRel|?|u|?|u (composeRel P);
Intros S T SsubT x z _;
Refine impliesRelE;Immed;
Refine transSubRel;Immed;
Refine impliesRelI;Refine reflSubRel;
Save composeRelMonoL;

[composeRelR [S:Rel t u][R:Rel s t] = composeRel R S];

Goal composeRelMonoR : monotoneRel|s|?|s|? (composeRelR Q);
Intros S T SsubT x z _;
Refine coimpliesRelE;Immed;
Refine transSubRel;Immed;
Refine coimpliesRelI;Refine reflSubRel;
Save composeRelMonoR;

Goal composeRelEqL1 : SubRel (composeRel (Eq|s) P) P;
Intros;Refine hyp;Intros x eq _;
Qrepl eq; Immed;
Save composeRelEqL1;

Goal composeRelEqL2 : SubRel P (composeRel (Eq|s) P); 
Intros;Refine  ex_y;Refine +1 Eq_refl;Immed;
Save composeRelEqL2;

Goal composeRelEqR1 : SubRel (composeRel P (Eq|t)) P;
Intros;Refine hyp;Intros y _ eq;Qrepl Eq_sym eq;Immed;
Save composeRelEqR1;

Goal composeRelEqR2 : SubRel P (composeRel P (Eq|t)); 
Intros;Refine ex_y;Refine +2 Eq_refl;Immed;
Save composeRelEqR2;

Goal composeRelAssoc1 : SubRel (composeRel(composeRel P Q) R) (composeRel P (composeRel Q R));
Intros x w ___;Refine hyp;
intros z hypPQ hypR;Refine hypPQ;
intros _ hypP hypQ;Refine ex_y;Immed;
Intros _ ex_z;Refine ex_z;Immed;
Save composeRelAssoc1;

Goal composeRelAssoc2 : SubRel (composeRel P (composeRel Q R)) (composeRel(composeRel P Q) R);
Intros x w __ ex_z;Refine hyp;
intros _ hypP hypQR;Refine hypQR;
intros z hypQ hypR;Refine ex_z;Immed;
Intros;Refine ex_y;Immed; 
Save composeRelAssoc2;

Goal opcompose1 : SubRel (composeRel (op Q) (op P)) (op (composeRel P Q));
Intros;Refine hyp;intros;Refine ex_y;Immed;
Save opcompose1;

Goal opcompose2 : SubRel (op (composeRel P Q)) (composeRel (op Q) (op P));
Intros;Refine hyp;intros;Refine ex_y;Immed;
Save opcompose2;

(* an interesting structure present on the endorelations *)

(* for want of a better term, kernels-left, right and symmetric *)
[S:Rel s s][T:Rel t t];

[ClosedL [R:Rel s t] = SubRel (composeRel S R) R];
[ClosedR [R:Rel s t] = SubRel (composeRel R T) R];

[symkernelRel = andRel (impliesRel S S) (coimpliesRel S S)];

DischargeKeep s;

Goal prekernelRelR : [P=impliesRel S S]and (preorder P) ({Q:Rel s s}(ClosedR Q S)->(SubRel Q P));

Refine pair;Refine pair;
Intros;Immed;
Intros;
Intros;Refine H1;Refine H;Immed;
Intros;Refine impliesRelI;Immed;

Save prekernelRelR;

(*[rightkernelRel = andRel (impliesRel S S) (coimpliesRel (op S) (op S))];
Goal kernelRelR : [kerR = rightkernelRel]and (equiv kerR)
                                  ({Q:Rel s s}(ClosedR Q S)->SubRel Q kerR);
 not quite right yet
Save kernelRelR;*)

Goal prekernelRelL : [P=coimpliesRel S S]and (preorder P)
                             ({Q:Rel s s}(ClosedL Q S)->(SubRel Q P));

Refine pair;Refine pair;
Intros;Immed;
Intros;
Intros;Refine H;Refine H1;Immed;
Intros;Refine coimpliesRelI;Immed;

Save prekernelRelL;

(*[leftkernelRel = andRel (impliesRel (op S) (op S)) (coimpliesRel S S)];
Goal kernelRelL : [kerL = leftkernelRel]and (equiv kerL)
                                 ({Q:Rel s s}(ClosedL Q S)->SubRel Q kerL);
 not quite right yet either
Save kernelRelL;*)

Goal kernelRel : (sym S) -> [kerS=symkernelRel S]and (equiv kerS)
                ({Q:Rel s s}(ClosedL Q S)->(ClosedR Q S)->SubRel Q kerS);

Intros symhyp;
Refine pair;
(* first conjunct - it's an equivalence *)
Refine pair;
(* refl *)
Intros x;Refine pair;
 Intros;Immed;
 Intros;Immed;
Refine pair;
(* sym *)
Intros x y hyp;
Refine hyp;intros SSxy SSyx;
Refine pair;
Intros;Refine symhyp;Refine SSyx;Refine symhyp;Immed;
Intros;Refine symhyp;Refine SSxy;Refine symhyp;Immed;
(* trans *)
Intros x y z lhyp rhyp;
Refine lhyp;Refine rhyp;intros SSyz SSzy SSxy SSyx;Refine pair;
Intros;Refine SSyz;Refine SSxy;Immed;
Intros;Refine SSyx;Refine SSzy;Immed;
(* second conjunct - the interesting property: it's the largest *)
intros;
Refine andRelI;
Refine impliesRelI;
Refine +1 coimpliesRelI;
Immed;

Save kernelRel;

Discharge s;

(* this concludes the "purely" algebraic properties  *)
(* of SubRel, now come some of the "infinitary" ones *)
