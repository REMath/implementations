:- use_module('write_ast.pl').
:- use_module('approx_eval.pl', [statement/3 as clpStatement, emptyState/2 as clpEmptyState]).
:- use_module('evaluation', [doEvaluation/5 as doesEvaluation]).
:- use_module(library(random)).

ensureNonvar(X, Err) :-
        nonvar(X) -> true; throw(Err).

% makes it so SWI-PL's output isn't shortened.
remove_max_depth:-
        set_prolog_flag(toplevel_print_options, [quoted(true), portray(true)]).

chooseSet([Head|_], Head).
chooseSet([_|Rest], X) :-
	chooseSet(Rest, X).

setContains(Set, N2) :-
        ensureNonvar(Set, 'Set cannot be a variable (setContains/1.1)'),
        Set = [N1|_],
	N1 == N2, !.
setContains(Set, N) :-
        ensureNonvar(Set, 'Set cannot be a variable (setContains/1.2)'),
        Set = [_|Rest],
	setContains(Rest, N), !.

addSet(List, Item, List) :-
	setContains(List, Item).
addSet(List, Item, [Item|List]) :-
	\+ setContains(List, Item).

setUnion([], S, S).
setUnion([Head|Tail], S, Res) :-
	addSet(S, Head, Temp),
	setUnion(Tail, Temp, Res).
        
% AST Definition:
% Note: \vec{...} permits an empty sequence
% n \in Integer
% b \in Boolean
% str \in String
% x \in Variable
% uop \in UnOp ::= void | typeof | + | - | ~ | !
% cbop \in CompoundBinOp ::= + | - | * | / | << | >> | >>> | & | `|` | ^
% bop \in BinOp ::= cbop | < | <= | > | >= | == | != | === | !== | && | `||` | in | , |
%                   instanceof
% regex \in Regex
% lbl \in Label
% sw \in SwitchComponent ::= case e s | default s
% e \in Expression ::= n | b | str | null | x | x = e | x cbop= e | e.e = e | e.e op= e | regex |
%                      e ? e : e | e.e | new e(\vec{e}) | e(\vec{e}) | function [x](\vec{x}) s |
%                      e bop e | uop e | \{ \vec{<str, e>} \} | [\vec{e}] | this |
%                      delete e | ++x | ++e.e | x++ | e.e++ | --x | --e.e | x-- | e.e-- |
%                      eval s
% the statement s in eval is treated specially; see write_ast.pl for details
% s \in Statement :: = e | \vec{s} | while e s | do s while e | for x in s | for e.e in s |
%                      for(s;e;s) s | var x = e[,x = e...] | function x(\vec{x}) s | if (e) s [s] |
%                      try s [x s] [s] | throw e | lbl: s | break [lbl] | continue [lbl] |
%                      with e s | return [e] | switch e \vec{sw}
%
% ADDITIONAL INVARIANTS:
% -Labels and variables are scoped
% -Switch can contain at most one default
% -Continue can only be contained in a loop.
% -If a label is provided to continue, the label must be on a scoped loop
% -Return can only be contained in a function
%
% DATA STRUCTURES:
% To maintain auxiliary information for invariants, some additional
% information must be stored.  This is in a state(...) structure.
% Form:
% state(VarsInScope, FunctionVarsInScope, LabelsInScope,
%       ContinueableLabels, InLoop, InFunction, Bound)

% TODO: these are here to abstract what State looks like,
% in case we have to add/remove from State later.  This is
% still ugly because each forces a particular size, but I'm
% not sure what can be done about that

emptyState(state([], [], [], [], false, false, Bound), Bound).
varsInScope(state(Vars, _, _, _, _, _, _), Vars).
functionsInScope(state(_, Vars, _, _, _, _, _), Vars).
labelsInScope(state(_, _, Labels, _, _, _, _), Labels).
continueLabels(state(_, _, _, Labels, _, _, _), Labels).
inLoop(state(_, _, _, _, InLoop, _, _), InLoop).
inFunction(state(_, _, _, _, _, InFunction, _), InFunction).
bound(state(_, _, _, _, _, _, Bound), Bound).

% When we use eval, we lose information pertaining to labels in
% scope and whether or not we are in a {function, loop}.  For example, the
% following code would result in a syntax error at runtime when
% we attempt to evaluate the eval:
%
% while (true) {
%   eval('break;');
% }
%
% evalReset: (OldState, NewState)
evalReset(state(Vars, FVars, _, _, _, _, Bound),
	  state(Vars, FVars, [], [], false, false, Bound)).

% evalRestore: (StateBeforeEval, StateAfterEval, NewState)
evalRestore(state(_, _, Labels, CLabels, InLoop, InFunction, _),
	    state(Vars, FVars, _, _, _, _, Bound),
	    state(Vars, FVars, Labels, CLabels, InLoop, InFunction, Bound)).

% withBound: (OldState, Bound, NewState)
withBound(state(V, F, L, C, IL, IF, _), Bound,
          state(V, F, L, C, IL, IF, Bound)).

% withBoundFromState: (BaseState, StateWithBound, NewState)
withBoundFromState(Base, WithBound, New) :-
        bound(WithBound, Bound),
        withBound(Base, Bound, New).

% Bound is intentionally left vague, as there are different metrics
% Decreases the bound, resulting in a new state.  This fails if the
% bound cannot go any lower.
decBound(state(V, F, L, C, IL, IF, OB),
         state(V, F, L, C, IL, IF, NB)) :-
        OB > 0,
        NB is OB - 1.

varInScope(X, State) :-
        varsInScope(State, Vars),
        chooseSet(Vars, X).
%        setContains(Vars, X).
varInFunctions(X, State) :-
        functionsInScope(State, FVars),
        chooseSet(FVars, X).
%        setContains(FVars, X).

labelInScope(Lbl, State) :-
        labelsInScope(State, Labels),
        chooseSet(Labels, Lbl).
%        setContains(Labels, Lbl).

% We can break either if we don't have a label and we're in a loop,
% or if we have a label that's in scope
% canBreak: (option(Label), State)
canBreak(none, State) :-
        inLoop(State, true).
canBreak(some(Label), State) :-
        labelInScope(Label, State).

% We can continue either if we don't have a label and we're in a loop,
% or if we have a continuable label
% canContinue: (option(Label), State)
canContinue(none, State) :-
        inLoop(State, true).
canContinue(some(Label), State) :-
        continueLabels(State, Labels),
        setContains(Labels, Label).

prePostIncDec(preIncVar(_)) :- maybe(0.2).
prePostIncDec(preIncUpd(_, _)) :- maybe(0.2).
prePostIncDec(postIncVar(_)) :- maybe(0.8).
prePostIncDec(postIncUpd(_, _)) :- maybe(0.5).
prePostIncDec(preDecVar(_)) :- maybe(0.8).
prePostIncDec(preDecUpd(_, _)) :- maybe(0.4702479221047986).
prePostIncDec(postDecVar(_)) :- maybe(0.8).
prePostIncDec(postDecUpd(_, _)) :- maybe(0.8).

% enteringFunction: (WithVars, Option(name), OldState, NewState)
enteringFunction(WithVars, none, 
                 state(OldVars, Functions, _, _, _, _, Bound),
                 state(NewVars, Functions, [], [], false, true, Bound)) :-
        setUnion(WithVars, OldVars, NewVars).
enteringFunction(WithVars, some(Name),
                 state(OldVars, OldFunctions, _, _, _, _, Bound),
                 state(NewVars, NewFunctions, [], [], false, true, Bound)) :-
        setUnion(WithVars, OldVars, NewVars),
        addSet(OldFunctions, Name, NewFunctions).

% addLabelInScope: (Label, InContinue, IState, OState)
% InContinue is a boolean used to determine whether or not
% we should add to the continuable labels as well
addLabelInScope(Lbl,
                state(V, F, OL, CL, IL, IF, B),
                state(V, F, NL, CL, IL, IF, B)) :-
        addSet(OL, Lbl, NL).

addVarsInScope(Vars,
               state(OV, F, L, CL, IL, IF, B),
               state(NV, F, L, CL, IL, IF, B)) :-
        setUnion(OV, Vars, NV).

% A try block must have either a catch, a finally, or both.  It
% cannot be missing these components
validCatchFinally(none, some(_)) :- maybe(0.5).
validCatchFinally(some(_), none) :- maybe(0.39973358586645535).
validCatchFinally(some(_), some(_)) :- maybe(0.5).

unop(void) :- maybe(0.2).
unop(typeof) :- maybe(0.2).
unop(uplus) :- maybe(0.2).
unop(uminus) :- maybe(0.27586411028157154).
unop(bitnot) :- maybe(0.8).
unop(lognot) :- maybe(0.2).

compoundBinop(plus) :- maybe(0.2).
compoundBinop(minus) :- maybe(0.8).
compoundBinop(mul) :- maybe(0.2).
compoundBinop(div) :- maybe(0.2).
compoundBinop(lshift) :- maybe(0.46021761799526906).
compoundBinop(rshift) :- maybe(0.49818293559254534).
compoundBinop(urshift) :- maybe(0.8).
compoundBinop(bitand) :- maybe(0.2).
compoundBinop(bitor) :- maybe(0.2).
compoundBinop(bitxor) :- maybe(0.2).

binop(A) :-
    maybe(0.2),
    compoundBinop(A).
binop(lt) :- maybe(0.5869507656651305).
binop(le) :- maybe(0.2).
binop(gt) :- maybe(0.2).
binop(ge) :- maybe(0.2).
binop(eq) :- maybe(0.2).
binop(ne) :- maybe(0.6045763285932102).
binop(equiv) :- maybe(0.36637142789649874).
binop(nequiv) :- maybe(0.5).
binop(logand) :- maybe(0.5448438625265171).
binop(logor) :- maybe(0.8).
binop(in) :- maybe(0.2).
binop(comma) :- maybe(0.2).
binop(instanceof) :- maybe(0.5).

% TODO: I'm not worrying about regexes for now.

switchComponents(Components, IState, OState) :-
    switchComponents(Components, false, IState, OState).

% switchComponents: (Components, SeenDefault, IState, OState)
switchComponents([], _, State, State).
switchComponents([case(E, S)|Tail], SeenDefault, IState, OState) :-
        decBound(IState, IStateB),
        expression(E, IStateB, TState1),
        statement(S, TState1, TState2),
        switchComponents(Tail, SeenDefault, TState2, OState).
switchComponents([default(S)|Tail], false, IState, OState) :-
        decBound(IState, IStateB),
        statement(S, IStateB, TState),
        switchComponents(Tail, true, TState, OState).

expressions([], State, State).
expressions([Head|Tail], IState, OState) :-
        decBound(IState, IStateB),
        expression(Head, IStateB, TState),
        expressions(Tail, TState, OState).

varlist([], State, State).
varlist([Head|Tail], IState, OState) :-
        decBound(IState, IStateB),
	% if the tail is a non-var, then this means we have a concrete
	% list of variables and we must check for uniqueness.  Otherwise
	% we don't need a uniqueness check.  This extra logic is neded
	% because setContains only operates on concrete sets
        (nonvar(Tail) -> (\+ setContains(Tail, Head)); true),
        varlist(Tail, IStateB, OState).

objBindings([], State, State).
objBindings([objBinding(_, E)|Rest], IState, OState) :-
        decBound(IState, IStateB),
        expression(E, IStateB, TState),
        objBindings(Rest, TState, OState).

declBindings([], State, State).
declBindings([binding(X, E)|Tail], IState, OState) :-
        decBound(IState, IStateB),
        addVarsInScope([X], IStateB, TState1),
        expression(E, TState1, TState2),
        declBindings(Tail, TState2, OState).

expression(num(_), State, State) :- maybe(0.2).
expression(bool(_), State, State) :- maybe(0.2).
expression(str(_), State, State) :- maybe(0.2).
expression(null, State, State) :- maybe(0.6042746150323908).
% because `this` behaves differently in node and spidermonkey anyway, at
% the moment we don't emit it at all.
%expression(this, State, State).
expression(var(X), State, State) :-
    maybe(0.2),
    (varInScope(X, State) ; varInFunctions(X, State)).
expression(simpleAssign(X, E), IState, OState) :-
        decBound(IState, IStateB),
        varInScope(X, IStateB),
	maybe(0.3354752384206031),
        expression(E, IStateB, OState).
expression(compoundAssign(X, Op, E), IState, OState) :-
        decBound(IState, IStateB),
        varInScope(X, IStateB),
	maybe(0.6275216789850563),
        compoundBinop(Op),
        expression(E, IStateB, OState).
expression(simpleUpdate(E1, E2, E3), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.5252420198429044),
        expression(E1, IStateB, TState1),
        expression(E2, TState1, TState2),
        expression(E3, TState2, OState).
expression(compoundUpdate(E1, E2, Op, E3), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.8),
        expression(E1, IStateB, TState1),
        expression(E2, TState1, TState2),
        compoundBinop(Op),
        expression(E3, TState2, OState).
expression(ternary(E1, E2, E3), IState, OState) :-
	decBound(IState, IStateB),
	maybe(0.39081980591141086),
	expression(E1, IStateB, TState1),
	expression(E2, TState1, TState2),
	expression(E3, TState2, OState).
expression(access(E1, E2), IState, OState) :-
	decBound(IState, IStateB),
	maybe(0.2),
	expression(E1, IStateB, TState),
	expression(E2, TState, OState).
expression(new(E, Es), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.2),
        expression(E, IStateB, TState),
        expressions(Es, TState, OState).
expression(call(E, Es), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.7767618327808115),
        expression(E, IStateB, TState),
        expressions(Es, TState, OState).
expression(functionExpr(FName, Xs, S), IState, OState) :-
        decBound(IState, IStateB1),
	maybe(0.2668374684754951),
        varlist(Xs, IStateB1, IStateB2),
        enteringFunction(Xs, FName, IStateB2, TState),
        statement(S, TState, InnerState),
        withBoundFromState(IStateB2, InnerState, OState).
expression(binop(E1, Op, E2), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.435634666117254),
        expression(E1, IStateB, TState),
        binop(Op),
        expression(E2, TState, OState).
expression(unop(Op, E), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.5),
        unop(Op),
        expression(E, IStateB, OState).
expression(object(Bindings), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.7218116315788621),
        objBindings(Bindings, IStateB, OState).
expression(array(Es), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.8),
        expressions(Es, IStateB, OState).
expression(delete(E), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.2966278136993183),
        expression(E, IStateB, OState).
expression(eval(S), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.2),
	evalReset(IStateB, TState1),
	statement(S, TState1, TState2),
	evalRestore(TState1, TState2, OState).
expression(PrePostIncDec, IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.8),
        prePostIncDec(PrePostIncDec),
        % FIXME: this is very fragile with the =..; very interdependent with
        % the prePostIncDec fact
        ((PrePostIncDec =.. [_, X],
         varInScope(X, IStateB),
         IStateB = OState);
        (PrePostIncDec =.. [_, E1, E2],
         expression(E1, IStateB, TState),
         expression(E2, TState, OState))).

statement(skip, State, State) :- maybe(0.8).
statement(E, IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.8),
        expression(E, IStateB, OState).
statement(seq(S1, S2), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.2),
        statement(S1, IStateB, TState),
        statement(S2, TState, OState).
%% statement(while(E, S), IState, OState) :-
%%         decBound(IState, IStateB),
%%         expression(E, IStateB, TState),
%%         statement(S, TState, OState).
%% statement(dowhile(S, E), IState, OState) :-
%%         decBound(IState, IStateB),
%%         statement(S, IStateB, TState),
%%         expression(E, TState, OState).
statement(forvarin(X, E, S), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.8),
        varInScope(X, IStateB),
        expression(E, IStateB, TState),
        statement(S, TState, OState).
statement(forupdin(E1, E2, E3, S), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.2),
        expression(E1, IStateB, TState1),
        expression(E2, TState1, TState2),
        expression(E3, TState2, TState3),
        statement(S, TState3, OState).
%% statement(for(E1, E2, E3, S), IState, OState) :-
%%         decBound(IState, IStateB),
%%         expression(E1, IStateB, TState1),
%%         expression(E2, TState1, TState2),
%%         expression(E3, TState2, TState3),
%%         statement(S, TState3, OState).
statement(vardecl(Bindings), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.6074180172398942),
        Bindings = [_|_],
        declBindings(Bindings, IStateB, OState).
statement(functionDecl(Name, Xs, S), IState, OState) :-
        decBound(IState, IStateB1),
	maybe(0.2),
        varlist(Xs, IStateB1, IStateB2),
        enteringFunction(Xs, some(Name), IStateB2, TState),
        statement(S, TState, InnerState),
        addVarsInScope([Name], IStateB2, WithFunc),
        withBoundFromState(WithFunc, InnerState, OState).
statement(if(E, S1, Option), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.2),
        expression(E, IStateB, TState1),
        statement(S1, TState1, TState2),
        ((Option = none, TState2 = OState);
         (Option = some(S2), statement(S2, TState2, OState))).
statement(try(S, Catch, Finally), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.8),
        statement(S, IStateB, TState1),
	validCatchFinally(Catch, Finally),
	(Catch = some(trybinding(X, S)) ->
	    (addVarsInScope([X], TState1, CatchState),
	     statement(S, CatchState, _)); 
	    true),
	(Finally = some(S2) ->
	    statement(S2, TState1, OState);
	    OState = TState1).
statement(throw(E), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.4604243757743504),
        expression(E, IStateB, OState).
statement(labeled(Lbl, S), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.2),
        addLabelInScope(Lbl, IStateB, TState),
        statement(S, TState, InnerState),
        withBoundFromState(IStateB, InnerState, OState).
statement(break(OLbl), IState, OState) :-
        decBound(IState, OState),
        canBreak(OLbl, IState),
	maybe(0.8).
statement(continue(OLbl), IState, OState) :-
        decBound(IState, OState),
        canContinue(OLbl, IState),
	maybe(0.8).
statement(with(E, S), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.2),
        expression(E, IStateB, TState),
        statement(S, TState, OState).
statement(return(OE), IState, OState) :-
        decBound(IState, IStateB),
        inFunction(IStateB, true),
	maybe(0.44830703505879577),
        ((OE = none, IStateB = OState);
         (OE = some(E),
          expression(E, IStateB, OState))).
statement(switch(E, Components), IState, OState) :-
        decBound(IState, IStateB),
	maybe(0.2),
	expression(E, IStateB, TState),
        switchComponents(Components, TState, OState).

objBindingGap(objBinding(_, E), E).
declBindingGap(binding(_, E), E).

switchComponentFold(case(E, S), pair(Ss, Es), pair([S|Ss], [E|Es])).
switchComponentFold(default(S), pair(Ss, Es), pair([S|Ss], Es)).

% gaps: (StmtOrExpression, Stmts, Exps)
gaps(num(_), [], []).
gaps(bool(_), [], []).
gaps(str(_), [], []).
gaps(null, [], []).
gaps(var(_), [], []).
gaps(simpleAssign(_, E), [], [E]).
gaps(compoundUpdate(E1, E2, _, E3), [], [E1, E2, E3]).
gaps(ternary(E1, E2, E3), [], [E1, E2, E3]).
gaps(access(E1, E2), [], [E1, E2]).
gaps(new(E, Es), [], [E|Es]).
gaps(call(E, Es), [], [E|Es]).
gaps(functionExpr(_, _, S), [S], []).
gaps(binop(E1, _, E2), [], [E1, E2]).
gaps(unop(_, E), [], [E]).
gaps(object(Bindings), [], Es) :-
        maplist(objBindingGap, Bindings, Es).
gaps(array(Es), [], Es).
gaps(delete(E), [], [E]).
gaps(eval(S), [S], []).
gaps(preIncVar(_), [], []).
gaps(preIncUpd(E1, E2), [], [E1, E2]).
gaps(postIncVar(_), [], []).
gaps(postIncUpd(E1, E2), [], [E1, E2]).
gaps(preDecVar(_), [], []).
gaps(preDecUpd(E1, E2), [], [E1, E2]).
gaps(postDecVar(_), [], []).
gaps(postDecUpd(E1, E2), [], [E1, E2]).
gaps(skip, [], []).
gaps(seq(S1, S2), [S1, S2], []).
%gaps(while(E, S), [S], [E]).
%gaps(dowhile(S, E), [S], [E]).
gaps(forvarin(_, E, S), [S], [E]).
gaps(forupdin(E1, E2, E3, S), [S], [E1, E2, E3]).
%gaps(for(E1, E2, E3, S), [S], [E1, E2, E3]).
gaps(vardecl(Bindings), [], Es) :-
        maplist(declBindingGap, Bindings, Es).
gaps(functionDecl(_, _, S), [S], []).
gaps(if(E, S, none), [S], [E]).
gaps(if(E, S1, some(S2)), [S1, S2], [E]).
gaps(try(S, none, none), [S], []).
gaps(try(S1, some(trybinding(_, S2)), none), [S1, S2], []).
gaps(try(S1, none, some(S2)), [S1, S2], []).
gaps(try(S1, some(trybinding(_, S2)), some(S3)), [S1, S2, S3], []).
gaps(throw(E), [], [E]).
gaps(labeled(_, S), [S], []).
gaps(break(_), [], []).
gaps(continue(_), [], []).
gaps(with(E, S), [S], [E]).
gaps(return(none), [], []).
gaps(return(some(E)), [], [E]).
gaps(switch(E, Components), Ss, [E|Es]) :-
        foldl(switchComponentFold, Components, pair([], []), pair(Ss, Es)).

% astContains: (A, PlacementClause, LookingForWhat, SeeingWhat)
% LookingForWhat and SeeingWhat can be either stmt or exp
astContains(A, PlacementClause, What, What) :-
        call(PlacementClause, A).
astContains(A, PlacementClause, LookingFor, _) :-
        gaps(A, Ss, Es),
        ((member(S, Ss),
          astContains(S, PlacementClause, LookingFor, stmt));
         (member(E, Es),
          astContains(E, PlacementClause, LookingFor, exp))).

% inSequence: [Clauses], Ast
inSequence([], skip).
inSequence(Items, seq(_, Rest)) :-
        Items = [_|_],
        inSequence(Items, Rest).
inSequence([HeadClause|RestClauses], seq(HeadStmt, RestStmts)) :-
        call(HeadClause, HeadStmt),
        inSequence(RestClauses, RestStmts).

% function foo(x, y, z) {
%   if (x > y) {
%     return x + y;
%   } else {
%     return y + z;
%   }
% }
% foo(1, 2, 3);
% foo(3, 2, 1);
test1(OState) :-
        S =
        seq(functionDecl(foo, [x, y, z], 
          if(binop(var(x), lt, var(y)),
             return(some(binop(var(x), plus, var(y)))),
             some(return(some(binop(var(y), plus, var(z))))))),
        seq(call(var(foo), [num(1), num(2), num(3)]),
        seq(call(var(foo), [num(3), num(2), num(1)]), skip))),
        emptyState(IState, 100),
        statement(S, IState, OState),
        writeOutStatement(S, 'test1_frompl.js').

test2 :-
    S = eval(eval(eval(binop(str(moo), plus, str(cow))))),
    emptyState(IState, 100),
    statement(S, IState, _),
    writeOutStatement(S, 'test2_frompl.js').

test3 :-
    Base = eval(eval(eval(binop(str(moo), plus, str(cow))))),
    emptyState(IState, 100),
    statement(Base, IState, _),
    withChainPrint(Header),
    writeOutStatement(seq(Header, call(var(chainPrint), [Base])), 'test3_frompl.js').

% should fail
test4 :-
    S = functionDecl(foo, [], eval(return(num(7)))),
    emptyState(IState, 100),
    statement(S, IState, _),
    writeOutStatement(S, 'test4_frompl.js').

testFunctionCallFunctionTemplate(Name, functionDecl(Name, _, _)).
testFunctionCallCallTemplate(Name, call(var(Name), _)). 
testFunctionCall(Stmt) :-
        call_with_depth_limit(
        inSequence([testFunctionCallFunctionTemplate(Name),
                    testFunctionCallCallTemplate(Name)],
                   Stmt), 4, Success),
        Success \== depth_limit_exceeded,
        format('~w~n', [Stmt]),
        emptyState(IState, 10),
        statement(Stmt, IState, _).

statement_(IState, Statement) :-
        statement(Statement, IState, _).
        %% catch((statement(Statement, IState, _), write(Statement), nl),
	%%       _,
	%%       halt).

go(Bound) :-
        emptyState(IState, Bound),
        writeStatements(statement_(IState), 'full', '.js').

matchesCLP(S) :-
    clpEmptyState(State, 1000),
    clpStatement(S, State, _).

:- dynamic seen/1.

% genAsts: (State, NumAsts, NumUnique, NumUniqueRes)
genAsts(_, 0, Accum, Accum) :- !.
genAsts(State, NumAsts, Seen, Result) :-
    !,
    statistics(runtime, [Total, _]),
    (Total > 720000 -> throw(time_limit_exceeded); true),
    (call_with_time_limit(10, statement(Statement, State, _)) ->
     (seen(Statement) -> Add = 0;
      (matchesCLP(Statement) ->
       (Add = 1,
	assert(seen(Statement)));
       (Add = 0)));
     (Add = 0)), !,
    NewSeen is Seen + Add,
    NewNum is NumAsts - 1,
    genAsts(State, NewNum, NewSeen, Result).

run :-
    retractall(seen(_)),
    emptyState(State, 7),
    catch(genAsts(State, 2500000, 0, Res), time_limit_exceeded, Res = -1),
    writeln(Res).

clpStatement_(State, Statement) :-
	clpStatement(Statement, State, _).

makeUnique(NonUnique, Unique) :-
	sort(NonUnique, Unique).

doEvaluation(Sec) :-
	emptyState(StoState, 7),
	clpEmptyState(ClpState, 7),
	doesEvaluation(statement_(StoState), clpStatement_(ClpState), makeUnique, Sec, result(TotalSto, UniqueSto, InterestingSto, TotalCLP)),
	format('Total Sto: ~w~nUnique Sto: ~w~nInteresting Sto: ~w~nTotal CLP: ~w~n',
	       [TotalSto, UniqueSto, InterestingSto, TotalCLP]).
