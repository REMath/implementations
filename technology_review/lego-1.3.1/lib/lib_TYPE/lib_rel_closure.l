(* /home/jhm/Lego/relclosure.l    based on                            *)

(* /home/rb/CAFR90/closure.l    Closure of a relation                 *)
(* Rod and Savi, 10th Jan, 1991, with trivial modifications to ensure *)
(* compatibility and subsequent development of the Scott-Tarski fixed *)
(* point theorems by me 14th-22nd January, and beyond                 *)

(* definition of a closure operation for a set *)
(* of relations closed under intersections     *)
(* we really need the proofs that all the concepts *)
(* are invariant under EQRel, EQPred               *)
(* CHANGES

   24 Jan 1996
   Thomas Schreiber <tms@dcs.ed.ac.uk>
   converted LEGO file to library compatible module for arbitrary equality *)

Module lib_rel_closure Import lib_more_induction lib_rel lib_nat_Le;

[s,t,u,v|Type];

(* intersection, union of a family of Rels *)
[intersectionRel [F:Pred(Rel s t)] = [x:s][y:t]{R:Rel s t}{FR:F R}R x y:Rel s t];

[unionRel [F:Pred(Rel s t)] = [x:s][y:t] 
          {phi:Prop}{exR:{R:Rel s t}{FR:F R}{hypR:R x y}phi}phi:Rel s t];

(* intersection, union of a family of Preds *)
[intersectionPred [G:Pred(Pred s)] = [x:s]{P:Pred s}{GP:G P}P x:Pred s];

[unionPred [G:Pred(Pred s)] = 
           [x:s]{phi:Prop}{exP:{P:Pred s}{GP:G P}{hypP:P x}phi}phi:Pred s];

[E,F|Pred(Rel s t)][G,H|Pred(Pred s)];
[R:Rel s t][P:Pred s];

Goal intersectionRelI : {cone:{S:Rel s t}(F S) -> SubRel R S}SubRel R (intersectionRel F);
Intros;Refine cone;Try Immed;
Save intersectionRelI;

Goal intersectionRelE : (F R) -> SubRel (intersectionRel F) R;
Intros;Refine hyp;Try Immed;
Save intersectionRelE;

Goal unionRelI : (F R) -> SubRel R (unionRel F);
Intros;Refine exR;Try Immed;
Save unionRelI;

Goal unionRelE : {cone:{S:Rel s t}(F S) -> SubRel S R}SubRel (unionRel F) R;
Intros;Refine hyp;intros;Refine cone;Try Immed;
Save unionRelE;

Goal intersectionPredI : {cone:{Q:Pred s}(G Q) -> SubPred P Q}SubPred P (intersectionPred G);
Intros;Refine cone;Try Immed;
Save intersectionPredI;

Goal intersectionPredE : (G P) -> SubPred (intersectionPred G) P;
Intros;Refine hyp;Try Immed;
Save intersectionPredE;

Goal unionPredI : (G P) -> SubPred P (unionPred G);
Intros;Refine exP;Try Immed;
Save unionPredI;

Goal unionPredE : {cone:{Q:Pred s}(G Q) -> SubPred Q P}SubPred (unionPred G) P;
Intros;Refine hyp;intros;Refine cone;Try Immed;
Save unionPredE;

Goal intReversesSubRel : {EsubF:SubPred E F}SubRel (intersectionRel F) (intersectionRel E);
Intros;Refine hyp;Refine EsubF;Try Immed;
Save intReversesSubRel;

Goal unionPreservesSubRel : {EsubF:SubPred E F}SubRel (unionRel E) (unionRel F);
Intros;Refine hyp;intros;Refine exR;Refine +1 EsubF;Try Immed;
Save unionPreservesSubRel;

Goal intReversesSubPred : {GsubH:SubPred G H}SubPred (intersectionPred H) (intersectionPred G);
Intros;Refine hyp;Refine GsubH;Try Immed;
Save intReversesSubPred;

Goal unionPreservesSubPred : {GsubH:SubPred G H}SubPred (unionPred G) (unionPred H);
Intros;Refine hyp;intros;Refine exP;Refine +1 GsubH;Try Immed;
Save unionPreservesSubPred;

Discharge E;

[F:Pred(Rel s t)];

[IntersectionClosed = {G:Pred(Rel s t)}{GsubF:SubPred G F}F(intersectionRel G)]; 
[UnionClosed = {G:Pred(Rel s t)}{GsubF:SubPred G F}F(unionRel G)];
[iclF:IntersectionClosed];

Goal intFhasF : F(intersectionRel F);
Refine iclF;Refine reflSubPred;
Save intFhasF;

[uclF:UnionClosed];

Goal unionFhasF : F(unionRel F);
Refine uclF;Refine reflSubPred;
Save unionFhasF;

DischargeKeep F;

[G:Pred(Rel s t)]; 
[iclG:IntersectionClosed G]; 
 
Goal iclAnd : IntersectionClosed (andPred F G);
 Intros __;
 andI;Refine iclF; Refine +1 iclG;
 Refine andPredE1;Refine +2 andPredE2;Try Immed;
Save iclAnd;

[uclG:UnionClosed G];

Goal uclAnd : UnionClosed (andPred F G);
 Intros __;
 andI;Refine uclF; Refine +1 uclG;
 Refine andPredE1;Refine +2 andPredE2;Try Immed;
Save uclAnd;

DischargeKeep s;

Goal iclRefl : IntersectionClosed (refl|s);
Intros;Refine GsubF;Try Immed;
Save iclRefl;
Goal iclSym : IntersectionClosed (sym|s);
Intros;Refine GsubF;Refine +1 H;Try Immed;
Save iclSym;
Goal iclTrans : IntersectionClosed (trans|s);
Intros;Refine GsubF;Refine +2 H;Refine +2 H1;Try Immed;
Save iclTrans;
Goal iclPreorder : IntersectionClosed (preorder|s);
Refine iclAnd;Refine iclRefl;Refine iclTrans;
Save iclPreorder;
Goal iclPer : IntersectionClosed (per|s);
Refine iclAnd;Refine iclSym;Refine iclTrans;
Save iclPer;
Goal iclEquiv : IntersectionClosed (equiv|s);
Refine iclAnd;Refine iclRefl;Refine iclAnd;Refine iclSym;Refine iclTrans;
Save iclEquiv;
Goal uclSym : UnionClosed (sym|s);
Intros;Refine H;Intros;Refine exR;Refine +2 GsubF;Try Immed;
Save uclSym;

(* closure of a relation R for a family F *)
[closure [R:Rel s t] = intersectionRel (andPred F (SubRel R))];

[R,S|Rel s t];

Goal iclSubRelR : IntersectionClosed (SubRel R);
Intros;Refine GsubF;Try Immed;
Save iclSubRelR;

[Rbounds [S:Rel s t] = SubRel S R];

Goal uclRbounds : UnionClosed Rbounds;
Intros;Refine hyp;intros;Refine GsubF;Try Immed;
Save uclRbounds;

Goal closureInc : SubRel R (closure R);
Refine iclSubRelR;Refine andPredE2;Refine +1 reflSubRel;
Save closureInc;

Goal closureI : F(closure R);
Refine iclF;Refine andPredE1;Refine +1 reflSubRel;
Save closureI;

Goal closureE : (F S) -> (SubRel R S) -> SubRel (closure R) S;
intros;Refine intersectionRelE;andI;Try Immed;
Save closureE;

Goal closureEderived : (F (andRel (closure R) S)) -> (SubRel R S) -> SubRel (closure R) S;
intros;Refine transSubRel;Refine +1 intersectionRelE;Refine +1 pair;
Refine +1 H;Refine andRelI;Refine closureInc;Try Immed;
Refine andRelE2;Refine +1 reflSubRel;
Save closureEderived;

Discharge R; 

[phi:(Rel s t) -> Rel s t];
[PreFix  [R: Rel s t] = SubRel R (phi R)];
[PostFix [R: Rel s t] = SubRel (phi R) R];
[Fix     [R: Rel s t] = EqRel R (phi R)];
[Increasing = {R:(Rel s t)} PreFix R];
[Idempotent = {R:(Rel s t)} PostFix (phi R)];
[Monotone = {R,S:(Rel s t)}(SubRel R S) -> (SubRel (phi R) (phi S))];
[Closure = and Increasing (and Idempotent Monotone)];

Goal pfp0 : PreFix (emptyRel|s|t);
Refine emptyRelI;
Save pfp0;

Goal pfp1 : PostFix (univRel|s|t);
Refine univRelI;
Save pfp1;

[phimono:Monotone];

Goal  iclPostFix : IntersectionClosed PostFix;
Intros;Refine GsubF;Refine +1 phimono;Try Immed;
Intros;Refine hyp1;Try Immed;
Save iclPostFix;

Goal  uclPreFix : UnionClosed PreFix;
Intros;Refine hyp;intros;
Refine phimono;Refine +2 GsubF;Try Immed;
Intros;Refine exR;Try Immed;
Save uclPreFix;

DischargeKeep phi;

Goal closureClosure : Closure closure;
andI;
(* Increasing closure *)
Intros R;Refine closureInc;
andI;
(* Idempotent closure *) 
Intros R;Refine closureE;
Refine closureI;Refine reflSubRel;
(* Monotone closure *) 
Intros R S RsubS;Refine closureE;
Refine closureI;Refine transSubRel;Try Immed;Refine closureInc;
Save closureClosure;

DischargeKeep F;

(* now comes the Scott-Tarski account of fixed-points of the *)
(* form "closure (PostFix phi) R", for some monotone phi     *)

[leastFixPoint = intersectionRel (PostFix phi)];

Goal lfplemma : Fix phi leastFixPoint;

andI;
Refine intersectionRelE;
Refine phimono;
Refine ?+1;
Refine intFhasF (PostFix phi);
Refine iclPostFix;
Refine phimono;
Save lfplemma;

[phipower [n:nat][R:Rel s t] = nat_elim ([_:nat]Rel s t) R ([_:nat]phi) n:Rel s t];
[phipower0 [n:nat] = phipower n (emptyRel|s|t):Rel s t];

Goal phipower1 : {R|Rel s t}{k|nat}(PreFix phi R) -> PreFix phi (phipower k R);
intros;
Refine nat_iter_induction [S:Rel s t](PreFix phi R)->PreFix phi S;
intros;Try Immed;
intros S __;Refine phimono;Refine H1;Try Immed;
Try Immed;
Save phipower1;

Goal phipower2 : {m|nat}PreFix phi (phipower0 m);
intros;Refine phipower1;Refine pfp0;
Save phipower2;

Goal phipower3 : {m,k|nat}SubRel (phipower0 m) (phipower0 (plus k m));

intros;
Refine nat_iter_induction [k:nat]SubRel (phipower0 m) (phipower0 k);
Refine reflSubRel;
intros n _;
Refine transSubRel;Try Immed;
Refine phipower2;
Save phipower3;

Goal phipower4 : {m,k|nat}SubRel (phipower k (phipower0 m)) (phipower0 (plus k m));

intros;
Refine nat_rec_induction [k,n:nat]SubRel (phipower k (phipower0 m)) (phipower0 n);
Refine reflSubRel;
intros l n _;Refine phimono;Try Immed;
Save phipower4;

Goal phipowersincrease : {m,n|nat}(Le m n) -> SubRel (phipower0 m) (phipower0 n);

intros;Refine H;
intros;
Qrepl Eq_sym H1;
Qrepl plus_commutes m t1;
Refine phipower3;
Save phipowersincrease;

[leastPreFixPoint = [x:s][y:t]Ex [n:nat]((phipower0 n) x y):Rel s t];
 
Goal lpfplemma1 : {n|nat}SubRel (phipower0 n) leastPreFixPoint;
Intros ____;exI ?;Try Immed;
Save lpfplemma1;

Goal lpfplemma : PreFix phi leastPreFixPoint;

Intros;
Refine hyp;
intros n phi0nxy;
Refine phimono;
Refine +2 phipower2;Try Immed;
Refine lpfplemma1;
Save lpfplemma;

Goal lfplemma1 : {n|nat}SubRel (phipower0 n) leastFixPoint;

intros;
Refine nat_iter_induction [R:Rel s t]SubRel R leastFixPoint;
Refine emptyRelI;
intros R RsubLFP;
Refine transSubRel;
Refine +2 iclPostFix;Refine ?+2;Try Immed;
Refine phimono;
Refine reflSubPred;
Save lfplemma1;

Goal ScottTarski1 : SubRel leastPreFixPoint leastFixPoint;

Intros;Refine hyp;
intros;Refine lfplemma1;Try Immed;
Save ScottTarski1;

[singletonPred [y:s] = [x:s]Eq x y:Pred s];
[singletonRel [x:s][y:t] = [w:s][z:t]and (Eq x w) (Eq y z):Rel s t];

[finitePred = intersectionPred 
 [F:Pred(Pred s)]and3 (F (emptyPred|s))
                      ({y|s}F(singletonPred y))
                      ({A,B|Pred s}(F A) -> (F B) -> F(orPred A B))];

[finiteRel = intersectionPred
 [F:Pred(Rel s t)]and3 (F (emptyRel|s|t))
                       ({x|s}{y|t}F(singletonRel x y))
                       ({R,S|Rel s t}(F R) -> (F S) -> F(orRel R S))];

(*Goal finitePredrec : {Pf:Pred s}{finitePf:finitePred Pf}
 {Phi:Pred(Pred s)}
 {empty:Phi([x:s]false)}
 {singleton:{x:s}Phi(singletonPred x)}
 {join:{P,Q:Pred s}{join_premP:finitePred P}{join_ihP:Phi P}
                   {join_premQ:finitePred Q}{join_ihQ:Phi Q} Phi (orPred P Q)}
  Phi Pf; (* a definable primitive recursor for finite subsets of a set *)

intros;Refine finitePf (andPred (finitePred|s) Phi);
Refine pair3;
 Refine pair;
 Intros;Refine and3_out1 GP;Try Immed;
intros;Refine pair;
       Intros;Refine and3_out2 GP;Try Immed;
intros;Refine H;Refine H1;
intros finiteB phiB finiteA phiA;Refine pair;
       Intros;Refine and3_out3 GP;Refine finiteA;Refine +1 finiteB;Try Immed;
Refine join;Try Immed;
intros;Try Immed;
Save finitePredrec;*)


Goal finitephipowersbound : {Xf|Rel s t}(finiteRel Xf) ->
        (SubRel Xf leastPreFixPoint) -> Ex [n:nat]SubRel Xf (phipower0 n);

Refine intersectionPredE
 [Xf:Rel s t](SubRel Xf leastPreFixPoint) -> Ex [n:nat]SubRel Xf (phipower0 n);
Refine pair3;
(* empty set *)
intros;exI ?;Refine zero;Refine emptyRelI;
(* singletons *)
intros;exE H ?;Try Immed;
Refine pair;Refine Eq_refl;Refine Eq_refl;
intros n _;exI ?;Try Immed;
Intros xn yn _;(* xn, yn might depend on n, but they don't *)
Refine hyp;intros eqx eqy;

Qrepl Eq_sym eqx;
Qrepl Eq_sym eqy; Try Immed;

(* binary unions *)
Intros _____;
Refine H;Refine transSubRel;Refine +1 orRelI1;Try Immed;Refine reflSubRel;intros nR _;
Refine H1;Refine transSubRel;Refine +1 orRelI2;Try Immed;Refine reflSubRel;intros nS _;

Refine ExIntro (plus nR nS);
Refine orRelE;
Refine transSubRel;Try Immed;Refine phipowersincrease;Refine Le_plus_lemma1;
Refine transSubRel;Try Immed;Refine phipowersincrease;Refine Le_plus_lemma2;
Save finitephipowersbound;

[Algebraic = {R|Rel s t}{x|s}{y|t}{phiRxy:phi R x y}{psi:Prop}
      {exRf:{Rf:Rel s t}{finRf:finiteRel Rf}{RfsubF:SubRel Rf R}{phiRfxy:phi Rf x y}
             psi}psi];

[algphi|Algebraic];

Goal ScottTarski2 : SubRel leastFixPoint leastPreFixPoint;

Refine intersectionRelE;

Intros;Refine algphi hyp;intros;
Refine finitephipowersbound;Try Immed;
intros n _;Refine H;Refine suc n;
Refine phimono;Try Immed;
Save ScottTarski2;

Goal ScottTarski : Fix phi leastPreFixPoint;
Refine lfplemma;intros;Refine pair;
Refine transSubRel;
Refine +2 phimono;
Refine transSubRel;Try Immed;
Refine ScottTarski1;
Refine ScottTarski2;
Refine transSubRel;
Refine +1  phimono;
Refine +2 transSubRel;Try Immed;
Refine ScottTarski1;
Refine ScottTarski2;
Save ScottTarski;

DischargeKeep phi;

(* Extensions of Tarski to jointly monotone families of operators *)
(* for use in solving the perm problem of append-closure.         *)
(* Commutativity is the essential property, I realised.           *)
(* Andrews had, too, in 1973: Resolution in Type Theory, JSL      *)

[psi:(Rel s t) -> Rel s t]; (* first of all, the case of a pair of operators *)
[psimono:Monotone psi];     (* compare Andrews' lemma in Coquand-Huet 85     *)
[F2 = andPred (PostFix phi) (PostFix psi)];

Goal icl2 : IntersectionClosed F2;
Refine iclAnd;
Refine iclPostFix;Refine phimono;
Refine iclPostFix;Refine psimono;
Save icl2;

[int2 = intersectionRel F2];
Goal jointpostfixpoint2 : and (PostFix phi int2) (PostFix psi int2);
Refine intFhasF F2;Refine icl2;
Save jointpostfixpoint2;

[Commphipsi [R:Rel s t] = EqRel (phi (psi R)) (psi (phi R))];
[comm2:Commphipsi int2];    (* this is the decisive property for Andrews     *)
Goal jointprefixpoint2 : and (PreFix phi int2) (PreFix psi int2);
andE jointpostfixpoint2;
andE comm2;
andI;
Refine intersectionRelE;andI;
Refine phimono;Refine +1 transSubRel;Refine +2 H3;Refine +1 phimono;Try Immed;
Refine intersectionRelE;andI;
Refine transSubRel;Refine +1 H2;Refine psimono;Refine +1 psimono;Try Immed;
Save jointprefixpoint2;

[phifamily:u -> (Rel s t) -> Rel s t]; (* now the general case of a family *)
[phifamilymono:{z:u}Monotone (phifamily z)];
[Ffamily = [R:Rel s t]{z:u}PostFix (phifamily z) R];

Goal iclfamily : IntersectionClosed Ffamily;
Intros;
Refine iclPostFix;Try Immed;
Refine phifamilymono;
Intros;Refine GsubF;Try Immed;
Save iclfamily;

[intfamily = intersectionRel Ffamily];

Goal jointpostfixpoint : {z:u}PostFix (phifamily z) intfamily;
Refine intFhasF Ffamily;Refine iclfamily;
Save jointpostfixpoint;

[Commfamily [R:Rel s t] = 
   {z,w:u}SubRel ((phifamily z)((phifamily w) R)) ((phifamily w)((phifamily z) R))];
[commphi:Commfamily intfamily];        (* here too, commutativity is the key *)


Goal jointprefixpoint : {z:u}PreFix (phifamily z) intfamily;
intros;
Refine intersectionRelE;
Intros w;
Refine transSubRel;
Refine +1 commphi;
Refine phifamilymono;
Refine iclfamily;
Refine reflSubPred;
Save jointprefixpoint;

(* relativising the foregoing to lpfp/lfp above R, *) 
(* for any pfp R, remains to be done !!            *)
DischargeKeep s;

(* now an application of all that has gone before *)
[reflop = [S:Rel s s](Eq|s)];
[symop = op|s|s];
[transop = [S:Rel s s]composeRel S S];

Goal reflopMono : Monotone reflop;
Intros ___;Refine reflSubRel;
Save reflopMono;

Goal symopMono : Monotone symop;
Intros __;Refine opMono;
Save symopMono;

Goal transopMono : Monotone transop;
Intros ___;Refine transSubRel;
Refine +1 composeRelMonoL;
Refine +2 composeRelMonoR;Try Immed;
Save transopMono;

Goal commreflsym : {R:Rel s s}(Commphipsi reflop symop R);
intros;Refine pair;
Refine Eq_sym;
Intros;Refine Eq_sym;Try Immed;
Save commreflsym;

Goal commsymtrans : {R:Rel s s}(Commphipsi symop transop R);
intros;Refine pair;
Refine opcompose2;Refine opcompose1;
Save commsymtrans;

Goal commtransrefl : {R:Rel s s}(Commphipsi transop reflop R);
intros;Refine pair;
Intros;Refine hyp;intros;Refine Eq_trans;Try Immed;
Intros;Refine ex_y;Try Immed;Refine Eq_refl;
Save commtransrefl;

[Refl = PostFix reflop];
[Sym = PostFix symop];
[Trans = PostFix transop];
(* etc., etc. *)

Discharge s;
