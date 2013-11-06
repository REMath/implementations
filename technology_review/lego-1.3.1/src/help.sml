(* Help message
   $Log: help.sml,v $
   Revision 1.7  1997/06/17 09:34:35  djs
   Version conflict repair.

   Revision 1.5  1997/05/08 13:48:48  tms
   o Added documentation for command UTac
   o Removed documentation for politically incorrect commands
       Freeze, UnFreeze, Load, ForgetMark

   Revision 1.4  1997/02/17 17:56:01  tms
   fixed typos

   Revision 1.3  1997/02/17 17:39:35  tms
   updated help for version 1.3 ALPHA
 *)

fun help() = message"\
\New Commands:\n\
\Configuration\n\
\  Configure Equality      sets up the equality to be used by\n\
\    ID1 ID2 ID3             Qrepl, Theorems, Inversion, Induction and Qnify\n\
\                            where ID1 is the name of the equality predicate,\n\
\                                  ID2 is the name of its reflexivity proof and\n\
\                                  ID3 is the name of its substitutivity proof\n\
\  Configure Infix S A P   introduces a new infix operator S with\n\
\                            priority P and associativity A.\n\
\                              S ::= + | - | / | * | << | >> | /\\ | \\/\n\
\                                      | |- | :: | &ID | @ID\n\
\                              A ::= left | right\n\
\                              P ::= 1..9\n\     
\Induction\n\
\  Induction ID            do induction on premise ID\n\
\  Induction NUM           do induction on NUM unnamed premise\n\
\  Induction TERM          abstract TERM from the goal, then do induction on it\n\
\Unification Problems\n\
\  Qnify NUM               considers leftmost NUM equational premises\n\
\  Qnify                   considers all equational premises\n\
\  Qnify ID                equivalent to Refine cut ID; Qnify 1\n\
\User-defined Tactics\n\
\  UTac ID                 executes the tactic ID\n\
\                          To add new tactics, use legoML and invoke Drop;\n\
\                          to enter the ML level. You can add any function\n\
\                          f:unit->unit via Tactics.add_tactic ID f;\n\
\                          The command lego() will return you to the LEGO level\n\
\                          Recall that you can save such extensions via\n\
\                          ExportState\n\
\Miscellaneous\n\
\  Assumption [NUM]        attempts to close goal NUM by an assumption\n\
\  Invert ID               invert ID\n\
\Tacticals\n\
\  -> Notice that backtracking is only possible in a proof state!\n\
\  EXPRSN1 Then EXPRSN2    evaluate EXPRSN1, if evaluation succeeds,\n\
\                            evaluate EXPRSN2 on all subgoals\n\
\  EXPRSN1 Else  EXPRSN2   evaluate EXPRSN1, if evaluation fails,\n\
\                            backtrack and evaluate EXPRSN2\n\
\  For n EXPRSN            evaluate EXPRSN Then EXPRSN Then ... (n times)\n\
\  Repeat EXPRSN           evaluate EXPRSN Then EXPRSN Then ... and backtrack\n\
\                            last failure\n\
\  Succeed                 this tactical doesn't do anything\n\
\  Fail                    this tactical always fails\n\
\  Try EXPRSN              evaluate EXPRSN and backtrack if evaluation fails\n\
\  (EXPRSN)                evaluate EXPRSN\n\n\
\Inductive declarations\n\
\  Inductive DECLS1        defines datatype(s) DECLS1 with constructors\n\
\    [Relation]            inductive relation\n\
\    [Inversion]           generate inversion theorem\n\
\    [Theorems]            proves some properties for *some* inductive declarations\n\
\    [ElimOver U]          the generated elimination rule constructs objects of type U (the default is TYPE)\n\
\    [Double]              generate nested double elimination rule\n\
\    [Parameters  DECS]         \n\
\    Constructors DECLS2        \n\
\    [NoReductions]        prevent generation of computation rules\n\
\Module concept\n\
\  Module ID               start a module named ID which requires modules\n\
\    [Import ID1 ID2 ..]        named ID1 ID2 ..\n\
\  Make ID                 process module ID\n\
\Basic Commands:\n\
\  Init TT[']              where TT is LF, PCC, CC, or XCC\n\
\      The optional ' requests maximal universe polymorphism.\n\
\  Goal [ID :] TERM        start named refinement proof with goal TERM\n\
\  Refine [NUM] TERM       refine goal NUM by TERM\n\
\  Intros [NUM] ID1 ID2 .. Pi-introductions on HNF of goal NUM\n\
\  intros [NUM] ID1 ID2 .. Pi-introductions on goal NUM\n\
\  Claim TERM              create a new goal (lemma) in a proof\n\
\  Equiv TERM              replace first goal with equivalent goal TERM\n\
\  Qrepl TERM              use the type of TERM as a conditional equation\n\
\                               to rewrite the current goal\n\
\  Prf                     show current proof state\n\
\  Save [ID]               save proof term as global with name ID\n\
\  $Save [ID]              save proof term as local with name ID\n\
\  KillRef                 kill the current refinement proof\n\
\  Discharge ID            discharge assumptions back to ID\n\
\  Help                 print this message\n\
\  Pwd                  print working directory\n\
\  Cd \"STRING\"          change directory\n\
\  Ctxt [n]             prints all (last n) context entries\n\
\  Decls [n]            prints all (last n) declarations (not definitions)\n\
\Basic Syntax: (some theories don't have 'Type' or Sigma)\n\
\  TERM ::= Prop | Type                     kinds\n\
\         | ID                              variable or constant\n\
\         | {x:TERM}TERM | TERM -> TERM     Pi\n\
\         | [x:TERM]TERM                    Lambda\n\
\         | TERM TERM                       application\n\
\         | TERM.TERM                       postfix application\n\
\         | TERM SYM TERM                   infix application\n\
\         | <x:TERM>TERM | TERM # TERM      Sigma\n\
\         | (TERM,TERM, ...)                tuple\n\
\         | (TERM,TERM,...:TERM)            annotated tuple\n\
\         | TERM.1 | TERM.2                 projections\n\
\         | (TERM : TERM)                   typecast\n\
\         | [x=TERM]TERM                    'let'\n\
\  CXT  ::= [] | CXT BIND                   context\n\
\  BIND ::= [x:TERM]                        local variable or assumption\n\
\         | [x=TERM]                        global definition\n\
\         | $[x:TERM]                       global variable or assumption\n\
\         | $[x=TERM]                       local definition\n\
\   *** There is much more info on the WWW\n\
\         http://www.dcs.ed.ac.uk/home/lego    ***";




