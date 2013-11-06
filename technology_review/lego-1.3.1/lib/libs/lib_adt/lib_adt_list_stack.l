(***********************************)
(* LEGO Summerschool August 1995   *)
(* Hetzelsdorf                     *)
(* Author: Zhaohui Luo             *)
(* Email: Zhaohui.Luo@durham.ac.uk *)
(***********************************)
Module lib_adt_list_stack Import lib_list_basics lib_adt_stack_cong;

(******************************************************
***** Concrete impl of stacks by lists (of nats) ******
******************************************************)

(*************************************
****** defn of module listStack ******
*************************************)

Goal listStack : Str_STACK;
Refine make_Str_STACK;
Refine make_Setoid nat.list (Eq|nat.list); (* domain and Leibniz's equality as eq *)
Refine nat.nil;				  (* empty stack *)
Refine cons|nat;			  (* push *)
Refine tail|nat;			  (* pop *)
Refine zero.hd;				  (* top *)
(* QED *)
Save listStack;


(***************************************
******* listStack realises STACK *******
****************************************)

(* EqSTACK *)
Goal eqStackL : 
     listStack.EqSTACK;
Refine pair3; Refine Eq_refl; Refine Eq_sym; Refine Eq_trans;
(* QED *)
Save eqStackL;

(* AxStack1 *)
Goal axStack1L : 
     listStack.AxSTACK1;
Refine Eq_refl;
(* QED *)
Save axStack1L;


(* AxSTACK2 *)
Goal axStack2L : 
     listStack.AxSTACK2; 
Refine Eq_refl;
(* QED *)
Save;

(* AxSTACK3 *)
Goal axStack3L : 
     listStack.AxSTACK3; 
Expand AxSTACK3; intros; Refine Eq_refl;
(* QED *)
Save;

(* AxSTACK4 *)
Goal axStack4L : 
     listStack.AxSTACK4; 
Expand AxSTACK4; intros; Refine Eq_refl;
(* QED *)
Save;

(* correctness proof *)

Goal listStack_correct : listStack.Ax_STACK;
Refine pair5; Refine eqStackL; 
Refine axStack1L; Refine axStack2L;
Refine axStack3L; Refine axStack4L;
Save;



(******************************************************
***** Concrete impl of stacks with cong by lists ******
******************************************************)

(* The extra axiom RespSTACK *)
Goal respStackL : 
     listStack.RespSTACK;
Refine pair3; 
Expand RespSTACKpush; intros; Qrepl H; Qrepl H1; Refine Eq_refl;
Expand RespSTACKpop;  intros; Qrepl H; Refine Eq_refl;
Expand RespSTACKtop;  intros; Qrepl H; Refine Eq_refl;
Save;

(* correctness proof *)

Goal listStack_correct_cong : STACK_CONG.Ax listStack;
Refine pair; Refine listStack_correct; Refine respStackL;
Save;

