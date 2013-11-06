(***********************************)
(* LEGO Summerschool August 1995   *)
(* Hetzelsdorf                     *)
(* Author: Zhaohui Luo             *)
(* Email: Zhaohui.Luo@durham.ac.uk *)
(***********************************)
Module lib_adt_stack_cong Import lib_adt_basics lib_adt_stack;

(*************************************
***** ADT STACK with eq as cong ******
**************************************)

(* extra axiom *)
[S:Str_STACK];
[RespSTACKpush= {n,m:nat}{s,s':S.Stack.dom}
		(Eq n m)->(eq s s')->eq (S.push n s) (S.push m s')];
[RespSTACKpop = {s,s':S.Stack.dom}(eq s s')->(eq (S.pop s) (S.pop s'))];
[RespSTACKtop = {s,s':S.Stack.dom}(eq s s')->(Eq  (S.top s) (S.top s'))];
[RespSTACK    = and3 RespSTACKpush RespSTACKpop RespSTACKtop];
Discharge S;

[STACK_CONG = Extend_AxOnly STACK RespSTACK : SPEC];


(***************************************************
***** some properties about stack operations *******
***************************************************)

[iterate [A|Type][f:A->A][n:nat][a:A] = nat_iter a f n];


[S:STACK_CONG.Str][ax:STACK_CONG.Ax S];

(* properties about pop.iterate *)

(* pop^{x+1}(s) = pop^x(pop(s)) *)
Goal pop_iterate : 
     {s:S.Stack.dom}{x:nat}eq (S.pop.iterate x.suc s) (S.pop.iterate x (S.pop s));
intros; Refine nat_ind [x:nat]eq (S.pop.iterate x.suc s) (S.pop.iterate x (S.pop s));
Refine ax.fst.and5_out1.and3_out1;
intros; Refine ax.snd.and3_out2; Refine H;
Save;

(* s=s' => pop^n(s) = pop^n(s') *)
Goal pop_iterate_resp : 
     {s,s':S.Stack.dom}(eq s s')->{x:nat}(eq (S.pop.iterate x s) (S.pop.iterate x s'));
intros; Refine nat_ind [x:nat] eq (iterate (pop S) x s) (iterate (pop S) x s');
Refine H; 
intros; Refine ax.snd.and3_out2; Refine H1;
Save;

(* pop^n(empty) = empty *)
Goal pop_iterate_empty : 
     {i:nat}eq (S.pop.iterate i S.empty) S.empty;
intros; Refine nat_ind[i:nat]eq (S.pop.iterate i S.empty) S.empty;
Refine ax.fst.and5_out1.and3_out1;
intros; 
Refine ax.fst.and5_out1.and3_out3; Refine S.pop S.empty;
Refine ax.snd.and3_out2; Refine H;
Refine ax.fst.and5_out2;
(* QED *)
Save;

(* pop^{k+1}(push(m,s)) = pop^k(s) *)
Goal pop_iterate_push : 
     {s:S.Stack.dom}{k,m:nat}eq (S.pop.iterate k.suc (S.push m s)) (S.pop.iterate k s);
intros; Refine nat_ind [k:nat]eq (S.pop.iterate k.suc (S.push m s)) (S.pop.iterate k s);
Refine ax.fst.and5_out4;
intros; Refine ax.snd.and3_out2; Refine H;
Save;

Discharge S;
