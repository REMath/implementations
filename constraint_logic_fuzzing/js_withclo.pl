:- use_module('with_closures_clp.pl', [withclo/1, basicGeneration/2 as clpGenerate, emptyState/2 as clpEmptyState]).
:- use_module('evaluation', [doEvaluation/5 as doesEvaluation]).

:- use_module('write_ast.pl').
:- use_module(library('random')).

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
%       ContinueableLabels, InLoop, InFunction, Bound, SeenWith, SeenClosure) % ADDITIONAL INVARIANTS

% TODO: these are here to abstract what State looks like,
% in case we have to add/remove from State later.  This is
% still ugly because each forces a particular size, but I'm
% not sure what can be done about that

emptyState(state([], [], [], [], false, false, Bound, false, false), Bound).
varsInScope(state(Vars, _, _, _, _, _, _, _, _), Vars).
functionsInScope(state(_, Vars, _, _, _, _, _, _, _), Vars).
labelsInScope(state(_, _, Labels, _, _, _, _, _, _), Labels).
continueLabels(state(_, _, _, Labels, _, _, _, _, _), Labels).
inLoop(state(_, _, _, _, InLoop, _, _, _, _), InLoop).
inFunction(state(_, _, _, _, _, InFunction, _, _, _), InFunction).
bound(state(_, _, _, _, _, _, Bound, _, _), Bound).
seenWith(state(_, _, _, _, _, _, _, SeenWith, _), SeenWith).
seenClosure(state(_, _, _, _, _, _, _, _, SeenClosure), SeenClosure).

setSeenWith(state(A, B, C, D, E, F, G, _, H), state(A, B, C, D, E, F, G, true, H)).
setSeenClosure(state(A, B, C, D, E, F, G, H, _), state(A, B, C, D, E, F, G, H, true)).

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
evalReset(state(Vars, FVars, _, _, _, _, Bound, SeenWith, SeenClosure),
	  state(Vars, FVars, [], [], false, false, Bound, SeenWith, SeenClosure)).

% evalRestore: (StateBeforeEval, StateAfterEval, NewState)
evalRestore(state(_, _, Labels, CLabels, InLoop, InFunction, _, _, _),
	    state(Vars, FVars, _, _, _, _, Bound, SeenWith, SeenClosure),
	    state(Vars, FVars, Labels, CLabels, InLoop, InFunction, Bound, SeenWith, SeenClosure)).

% withBound: (OldState, Bound, NewState)
withBound(state(V, F, L, C, IL, IF, _, SeenWith, SeenClosure), Bound,
          state(V, F, L, C, IL, IF, Bound, SeenWith, SeenClosure)).

% withBoundFromState: (BaseState, StateWithBound, NewState)
withBoundFromState(Base, WithBound, New) :-
        bound(WithBound, Bound),
        withBound(Base, Bound, New).

% Bound is intentionally left vague, as there are different metrics
% Decreases the bound, resulting in a new state.  This fails if the
% bound cannot go any lower.
decBound(state(V, F, L, C, IL, IF, OB, SeenWith, SeenClosure),
         state(V, F, L, C, IL, IF, NB, SeenWith, SeenClosure)) :-
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
                 state(OldVars, Functions, _, _, _, _, Bound, SeenWith, SeenClosure),
                 state(NewVars, Functions, [], [], false, true, Bound, SeenWith, SeenClosure)) :-
        setUnion(WithVars, OldVars, NewVars).
enteringFunction(WithVars, some(Name),
                 state(OldVars, OldFunctions, _, _, _, _, Bound, SeenWith, SeenClosure),
                 state(NewVars, NewFunctions, [], [], false, true, Bound, SeenWith, SeenClosure)) :-
        setUnion(WithVars, OldVars, NewVars),
        addSet(OldFunctions, Name, NewFunctions).

% addLabelInScope: (Label, InContinue, IState, OState)
% InContinue is a boolean used to determine whether or not
% we should add to the continuable labels as well
addLabelInScope(Lbl,
                state(V, F, OL, CL, IL, IF, B, SeenWith, SeenClosure),
                state(V, F, NL, CL, IL, IF, B, SeenWith, SeenClosure)) :-
        addSet(OL, Lbl, NL).

addVarsInScope(Vars,
               state(OV, F, L, CL, IL, IF, B, SeenWith, SeenClosure),
               state(NV, F, L, CL, IL, IF, B, SeenWith, SeenClosure)) :-
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

expression(num(_), State, State) :- maybe(0.2).
%% expression(bool(_), State, State) :- maybe(BOOL_PROB).
%% expression(str(_), State, State) :- maybe(STR_PROB).
%% expression(null, State, State) :- maybe(NULL_PROB).
% because `this` behaves differently in node and spidermonkey anyway, at
% the moment we don't emit it at all.
%expression(this, State, State).
expression(var(X), State, State) :-
        maybe(0.5),
        varInScope(X, State) ; varInFunctions(X, State).
%% expression(simpleAssign(X, E), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(SIMPLE_ASSIGN_PROB),
%%         varInScope(X, IStateB),
%%         expression(E, IStateB, OState).
%% expression(compoundAssign(X, Op, E), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(COMPOUND_ASSIGN_PROB),
%%         varInScope(X, IStateB),
%%         compoundBinop(Op),
%%         expression(E, IStateB, OState).
%% expression(simpleUpdate(E1, E2, E3), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(SIMPLE_UPDATE_PROB),
%%         expression(E1, IStateB, TState1),
%%         expression(E2, TState1, TState2),
%%         expression(E3, TState2, OState).
%% expression(compoundUpdate(E1, E2, Op, E3), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(COMPOUND_UPDATE_PROB),
%%         expression(E1, IStateB, TState1),
%%         expression(E2, TState1, TState2),
%%         compoundBinop(Op),
%%         expression(E3, TState2, OState).
%% expression(ternary(E1, E2, E3), IState, OState) :-
%% 	decBound(IState, IStateB),
%%         maybe(TERNARY_PROB),
%% 	expression(E1, IStateB, TState1),
%% 	expression(E2, TState1, TState2),
%% 	expression(E3, TState2, OState).
%% expression(access(E1, E2), IState, OState) :-
%% 	decBound(IState, IStateB),
%%         maybe(ACCESS_PROB),
%% 	expression(E1, IStateB, TState),
%% 	expression(E2, TState, OState).
%% expression(new(E, Es), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(NEW_PROB),
%%         expression(E, IStateB, TState),
%%         expressions(Es, TState, OState).
expression(call(E, Es), IState, OState) :-
        decBound(IState, IStateB),
        maybe(0.8),
        expression(E, IStateB, TState),
        expressions(Es, TState, OState).
%% expression(functionExpr(FName, Xs, S), IState, OState2) :-
%%         decBound(IState, IStateB1),
%%         maybe(FUNCTION_EXPR_PROB),
%%         varlist(Xs, IStateB1, IStateB2),
%%         enteringFunction(Xs, FName, IStateB2, TState),
%%         statement(S, TState, InnerState),
%%         withBoundFromState(IStateB2, InnerState, OState1),
%% 	setSeenClosure(OState1, OState2).
%% expression(binop(E1, Op, E2), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(BINOP_PROB),
%%         expression(E1, IStateB, TState),
%%         binop(Op),
%%         expression(E2, TState, OState).
%% expression(unop(Op, E), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(UNOP_PROB),
%%         unop(Op),
%%         expression(E, IStateB, OState).
%% expression(object(Bindings), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(OBJECT_PROB),
%%         objBindings(Bindings, IStateB, OState).
%% expression(array(Es), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(ARRAY_PROB),
%%         expressions(Es, IStateB, OState).
%% expression(delete(E), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(DELETE_PROB),
%%         expression(E, IStateB, OState).
%% expression(eval(S), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(EVAL_PROB),
%% 	evalReset(IStateB, TState1),
%% 	statement(S, TState1, TState2),
%% 	evalRestore(TState1, TState2, OState).
%% expression(PrePostIncDec, IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(PRE_POST_INC_DEC_PROB),
%%         prePostIncDec(PrePostIncDec),
%%         % FIXME: this is very fragile with the =..; very interdependent with
%%         % the prePostIncDec fact
%%         ((PrePostIncDec =.. [_, X],
%%          varInScope(X, IStateB),
%%          IStateB = OState);
%%         (PrePostIncDec =.. [_, E1, E2],
%%          expression(E1, IStateB, TState),
%%          expression(E2, TState, OState))).

statement(skip, State, State) :- maybe(0.2).
statement(E, IState, OState) :-
        decBound(IState, IStateB),
        maybe(0.2358063527376446),
        expression(E, IStateB, OState).
statement(seq(S1, S2), IState, OState) :-
        decBound(IState, IStateB),
        maybe(0.5449073118938831),
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
%% statement(forvarin(X, E, S), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(FOR_VAR_IN_PROB),
%%         varInScope(X, IStateB),
%%         expression(E, IStateB, TState),
%%         statement(S, TState, OState).
%% statement(forupdin(E1, E2, E3, S), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(FOR_UPD_IN_PROB),
%%         expression(E1, IStateB, TState1),
%%         expression(E2, TState1, TState2),
%%         expression(E3, TState2, TState3),
%%         statement(S, TState3, OState).
%% statement(for(E1, E2, E3, S), IState, OState) :-
%%         decBound(IState, IStateB),
%%         expression(E1, IStateB, TState1),
%%         expression(E2, TState1, TState2),
%%         expression(E3, TState2, TState3),
%%         statement(S, TState3, OState).
%% statement(vardecl(Bindings), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(VAR_DECL_PROB),
%%         Bindings = [_|_],
%%         declBindings(Bindings, IStateB, OState).
statement(functionDecl(Name, Xs, S), IState, OState) :-
        decBound(IState, IStateB1),
        maybe(0.2),
        varlist(Xs, IStateB1, IStateB2),
        enteringFunction(Xs, some(Name), IStateB2, TState),
        statement(S, TState, InnerState),
        addVarsInScope([Name], IStateB2, WithFunc),
        withBoundFromState(WithFunc, InnerState, OState).
%% statement(if(E, S1, Option), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(IF_PROB),
%%         expression(E, IStateB, TState1),
%%         statement(S1, TState1, TState2),
%%         ((Option = none, TState2 = OState);
%%          (Option = some(S2), statement(S2, TState2, OState))).
%% statement(try(S, Catch, Finally), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(TRY_PROB),
%%         statement(S, IStateB, TState1),
%% 	validCatchFinally(Catch, Finally),
%% 	(Catch = some(trybinding(X, S)) ->
%% 	    (addVarsInScope([X], TState1, CatchState),
%% 	     statement(S, CatchState, _)); 
%% 	    true),
%% 	(Finally = some(S2) ->
%% 	    statement(S2, TState1, OState);
%% 	    OState = TState1).
%% statement(throw(E), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(THROW_PROB),
%%         expression(E, IStateB, OState).
%% statement(labeled(Lbl, S), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(LABELED_PROB),
%%         addLabelInScope(Lbl, IStateB, TState),
%%         statement(S, TState, InnerState),
%%         withBoundFromState(IStateB, InnerState, OState).
%% statement(break(OLbl), IState, OState) :-
%%         decBound(IState, OState),
%%         canBreak(OLbl, IState),
%%         maybe(BREAK_PROB).

%% statement(continue(OLbl), IState, OState) :-
%%         decBound(IState, OState),
%%         canContinue(OLbl, IState),
%%         maybe(CONTINUE_PROB).
statement(with(E, S), IState, OState2) :-
        decBound(IState, IStateB),
        maybe(0.8),
        expression(E, IStateB, TState),
        statement(S, TState, OState1),
	setSeenWith(OState1, OState2).
%% statement(return(OE), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(RETURN_PROB),
%%         inFunction(IStateB, true),
%%         ((OE = none, IStateB = OState);
%%          (OE = some(E),
%%           expression(E, IStateB, OState))).
%% statement(switch(E, Components), IState, OState) :-
%%         decBound(IState, IStateB),
%%         maybe(SWITCH_PROB),
%% 	expression(E, IStateB, TState),
%%         switchComponents(Components, TState, OState).

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

statement_(IState, seq(Header, Statement)) :-
    chainPrintHeader(Header),
    statement(Statement, IState, OState),
    seenWith(OState, true),
    seenClosure(OState, true).

go(Bound) :-
        emptyState(IState, Bound),
        writeStatements(statement_(IState), 'withclo', '.js').

% doCalc: (State, NumToMake, NumMade, NumMatchedAccum, NumMatched)
doCalc(_, ToMakeMade, ToMakeMade, NumMatched, NumMatched) :- !.
doCalc(State, NumToMake, NumMade, NumMatchedAccum, NumMatched) :-
        !,
        once(statement(Statement, State, _)),
        (once(withclo(Statement)) -> Add = 1; Add = 0),
        NewAccum is NumMatchedAccum + Add,
        NewNumMade is NumMade + 1,
        doCalc(State, NumToMake, NewNumMade, NewAccum, NumMatched).

calculateSpecificity(NumToMake, Ratio) :-
        emptyState(State, 13),
        doCalc(State, NumToMake, 0, 0, NumMatched),
        Ratio is NumMatched / NumToMake.

templateCalc(_, 0, Accum, Accum) :- !.
templateCalc(State, NumToMake, NumMatchedAccum, NumMatched) :-
	!, 
	statistics(runtime, [Total, _]),
	(Total > 360000 -> throw(time_limit_exceeded); true),
	(call_with_time_limit(5, statement(Statement, State, _)) ->
	    (once(template(Statement)) -> Add = 1; Add = 0);
	    (Add = 0)),
	NewAccum is NumMatchedAccum + Add,
	NewNumToMake is NumToMake - 1,
	templateCalc(State, NewNumToMake, NewAccum, NumMatched).

templateSpecificity(NumToMake, NumMatched) :-
	emptyState(State, 7),
	templateCalc(State, NumToMake, 0, NumMatched).

template(seq(with(_,functionDecl(X, _, _)), seq(call(var(X), _),skip))).
template(seq(with(_,functionDecl(X,_,_)),seq(_,seq(call(var(X),_),skip)))).

run :-
	catch(templateSpecificity(2500000, NumMatched), time_limit_exceeded, NumMatched = -1),
	format('~w~n', [NumMatched]), !.
run :-
	write(-1), nl.

testTemplate(State, Statement) :-
	%template(Statement),
	statement(Statement, State, _).

makeUnique(NonUnique, Unique) :-
	sort(NonUnique, Unique).

doEvaluation(Secs) :-
	emptyState(State, 15),
	clpEmptyState(ClpState, 15),
	doesEvaluation(testTemplate(State), clpGenerate(ClpState), makeUnique, Secs, result(TotalSto, UniqueSto, InterestingSto, TotalCLP)),
	format('Total Sto: ~w~nUnique Sto: ~w~nInteresting Sto: ~w~nTotal CLP: ~w~n',
	       [TotalSto, UniqueSto, InterestingSto, TotalCLP]).
