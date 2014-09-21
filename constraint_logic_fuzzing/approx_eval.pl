:- module('approx_eval', [statement/3, emptyState/2]).

:- use_module(library(random)).
:- use_module('write_ast.pl').
:- use_module('approx_evaluator.pl').

nonNullUndefExp(E, State, NewState) :-
	bound(State, Bound),
	NewBound is max(Bound - 2, 1),
	call_with_depth_limit(anythingButNullUndefExp(E), NewBound, Fail),
	Fail \== depth_limit_exceeded,
	expression(E, State, NewState).
callableExp(E, State, NewState) :-
	bound(State, Bound),
	NewBound is max(Bound - 2, 1),
	call_with_depth_limit(canBeCalledExp(E), NewBound, Fail),
	Fail \== depth_limit_exceeded,
	expression(E, State, NewState).

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

prePostIncDec(preIncVar(_)).
prePostIncDec(preIncUpd(_, _)).
prePostIncDec(postIncVar(_)).
prePostIncDec(postIncUpd(_, _)).
prePostIncDec(preDecVar(_)).
prePostIncDec(preDecUpd(_, _)).
prePostIncDec(postDecVar(_)).
prePostIncDec(postDecUpd(_, _)).

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
validCatchFinally(none, some(_)).
validCatchFinally(some(_), none).
validCatchFinally(some(_), some(_)).

unop(void).
unop(typeof).
unop(uplus).
unop(uminus).
unop(bitnot).
unop(lognot).

compoundBinop(plus).
compoundBinop(minus).
compoundBinop(mul).
compoundBinop(div).
compoundBinop(lshift).
compoundBinop(rshift).
compoundBinop(urshift).
compoundBinop(bitand).
compoundBinop(bitor).
compoundBinop(bitxor).

binop(A) :-
        compoundBinop(A).
binop(lt).
binop(le).
binop(gt).
binop(ge).
binop(eq).
binop(ne).
binop(equiv).
binop(nequiv).
binop(logand).
binop(logor).
binop(in).
binop(comma).
binop(instanceof).

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

expression(num(_), State, State).
expression(bool(_), State, State).
expression(str(_), State, State).
expression(null, State, State).
% because `this` behaves differently in node and spidermonkey anyway, at
% the moment we don't emit it at all.
%expression(this, State, State).
expression(var(X), State, State) :-
        varInScope(X, State) ; varInFunctions(X, State).
expression(simpleAssign(X, E), IState, OState) :-
        decBound(IState, IStateB),
        varInScope(X, IStateB),
        expression(E, IStateB, OState).
expression(compoundAssign(X, Op, E), IState, OState) :-
        decBound(IState, IStateB),
        varInScope(X, IStateB),
        compoundBinop(Op),
        expression(E, IStateB, OState).
expression(simpleUpdate(E1, E2, E3), IState, OState) :-
        decBound(IState, IStateB),
        nonNullUndefExp(E1, IStateB, IStateB2),
        expression(E1, IStateB2, TState1),
        expression(E2, TState1, TState2),
        expression(E3, TState2, OState).
expression(compoundUpdate(E1, E2, Op, E3), IState, OState) :-
        decBound(IState, IStateB),
        nonNullUndefExp(E1, IStateB, IStateB2),
        expression(E1, IStateB2, TState1),
        expression(E2, TState1, TState2),
        compoundBinop(Op),
        expression(E3, TState2, OState).
expression(ternary(E1, E2, E3), IState, OState) :-
	decBound(IState, IStateB),
	expression(E1, IStateB, TState1),
	expression(E2, TState1, TState2),
	expression(E3, TState2, OState).
expression(access(E1, E2), IState, OState) :-
	decBound(IState, IStateB),
        nonNullUndefExp(E1, IStateB, IStateB2),
	expression(E1, IStateB2, TState),
	expression(E2, TState, OState).
expression(new(E, Es), IState, OState) :-
        decBound(IState, IStateB),
        callableExp(E, IStateB, IStateB2),
        expression(E, IStateB2, TState),
        expressions(Es, TState, OState).
expression(call(E, Es), IState, OState) :-
        decBound(IState, IStateB),
        callableExp(E, IStateB, IStateB2),
        expression(E, IStateB2, TState),
        expressions(Es, TState, OState).
expression(functionExpr(FName, Xs, S), IState, OState) :-
        decBound(IState, IStateB1),
        varlist(Xs, IStateB1, IStateB2),
        enteringFunction(Xs, FName, IStateB2, TState),
        statement(S, TState, InnerState),
        withBoundFromState(IStateB2, InnerState, OState).
expression(binop(E1, Op, E2), IState, OState) :-
        decBound(IState, IStateB),
        expression(E1, IStateB, TState),
        binop(Op),
        expression(E2, TState, OState).
expression(unop(Op, E), IState, OState) :-
        decBound(IState, IStateB),
        unop(Op),
        expression(E, IStateB, OState).
expression(object(Bindings), IState, OState) :-
        decBound(IState, IStateB),
        objBindings(Bindings, IStateB, OState).
expression(array(Es), IState, OState) :-
        decBound(IState, IStateB),
        expressions(Es, IStateB, OState).
expression(delete(E), IState, OState) :-
        decBound(IState, IStateB),
        nonNullUndefExp(E, IStateB, IStateB2),
        expression(E, IStateB2, OState).
expression(eval(S), IState, OState) :-
        decBound(IState, IStateB),
	evalReset(IStateB, TState1),
	statement(S, TState1, TState2),
	evalRestore(TState1, TState2, OState).
expression(PrePostIncDec, IState, OState) :-
        decBound(IState, IStateB),
        prePostIncDec(PrePostIncDec),
        % FIXME: this is very fragile with the =..; very interdependent with
        % the prePostIncDec fact
        ((PrePostIncDec =.. [_, X],
         varInScope(X, IStateB),
         IStateB = OState);
        (PrePostIncDec =.. [_, E1, E2],
         expression(E1, IStateB, TState),
         expression(E2, TState, OState))).

statement(skip, State, State).
statement(E, IState, OState) :-
        decBound(IState, IStateB),
        expression(E, IStateB, OState).
statement(seq(S1, S2), IState, OState) :-
        decBound(IState, IStateB),
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
        varInScope(X, IStateB),
        expression(E, IStateB, TState),
        statement(S, TState, OState).
statement(forupdin(E1, E2, E3, S), IState, OState) :-
        decBound(IState, IStateB),
        nonNullUndefExp(E1, IStateB, IStateB2),
        expression(E1, IStateB2, TState1),
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
        Bindings = [_|_],
        declBindings(Bindings, IStateB, OState).
statement(functionDecl(Name, Xs, S), IState, OState) :-
        decBound(IState, IStateB1),
        varlist(Xs, IStateB1, IStateB2),
        enteringFunction(Xs, some(Name), IStateB2, TState),
        statement(S, TState, InnerState),
        addVarsInScope([Name], IStateB2, WithFunc),
        withBoundFromState(WithFunc, InnerState, OState).
statement(if(E, S1, Option), IState, OState) :-
        decBound(IState, IStateB),
        expression(E, IStateB, TState1),
        statement(S1, TState1, TState2),
        ((Option = none, TState2 = OState);
         (Option = some(S2), statement(S2, TState2, OState))).
statement(try(S, Catch, Finally), IState, OState) :-
        decBound(IState, IStateB),
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
        expression(E, IStateB, OState).
statement(labeled(Lbl, S), IState, OState) :-
        decBound(IState, IStateB),
        addLabelInScope(Lbl, IStateB, TState),
        statement(S, TState, InnerState),
        withBoundFromState(IStateB, InnerState, OState).
statement(break(OLbl), IState, OState) :-
        decBound(IState, OState),
        canBreak(OLbl, IState).
statement(continue(OLbl), IState, OState) :-
        decBound(IState, OState),
        canContinue(OLbl, IState).
statement(with(E, S), IState, OState) :-
        decBound(IState, IStateB),
        expression(E, IStateB, TState),
        statement(S, TState, OState).
statement(return(OE), IState, OState) :-
        decBound(IState, IStateB),
        inFunction(IStateB, true),
        ((OE = none, IStateB = OState);
         (OE = some(E),
          expression(E, IStateB, OState))).
statement(switch(E, Components), IState, OState) :-
        decBound(IState, IStateB),
	expression(E, IStateB, TState),
        switchComponents(Components, TState, OState).

statement_(IState, Statement) :-
        statement(Statement, IState, _).
        %% catch((statement(Statement, IState, _), write(Statement), nl),
	%%       _,
	%%       halt).

%% go(Bound) :-
%%         emptyState(IState, Bound),
%%         writeStatements(statement_(IState), 'full', '.js').

statementLimitedCount(State, Bound, Statement) :-
    call_with_depth_limit(statement(Statement, State, _), Bound, Fail),
    Fail \== depth_limit_exceeded,
    maybe(0.0001),
    nb_getval(numgenerated, Count),
    (Count < 2500000 -> 
       (NewCount is Count + 1,
	nb_setval(numgenerated, NewCount));
       (!, true)).

go(Bound) :-
    emptyState(State, Bound),
    nb_setval(numgenerated, 0),
    writeStatements(statementLimitedCount(State, Bound), 'full_clp', '.js').

calcGenerationRate :-
	emptyState(State, 7),
	call_with_depth_limit(statement(_, State, _), 7, Fail),
	Fail \== depth_limit_exceeded,
	write(1), nl,
	statistics(runtime, [Total, _]),
	(Total >= 60000 -> halt; fail).

test1(S) :-
	S = seq(vardecl([binding(X, num(0))]),
	        compoundAssign(X, plus, num(0))),
	emptyState(State, 7),
	call_with_depth_limit(statement(S, State, _), 7, _).

test2(S) :-
	S = compoundUpdate(null, str('foo'), num(0)),
	emptyState(State, 7),
	call_with_depth_limit(statement(S, State, _), 7, _).
