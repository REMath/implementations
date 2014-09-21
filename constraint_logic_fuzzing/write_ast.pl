:- module(write_ast, [writeStatements/3,
		      writeOutStatement/2,
		      printingHeader/1,
		      chainPrintHeader/1]).
:- use_module(library(random)).
:- use_module(library(clpfd)).

% eval is handled as a special case
% whatever is passed to eval is treated as a string.
% This complicates things when nested evals occur, since we
% must put on a certain number of backslashes before any quote
% (specifically 2^n - 1 backlashes for level n nesting, starting
% from zero).
% We assume that single quotes are reserved for eval, and double
% quotes are reserved for constant strings.

% state representation: state(EvalLevel)
initialState(state(0)).
evalLevel(state(EvalLevel), EvalLevel).
setEvalLevel(state(_), Level, state(Level)).
incEvalLevel(state(EvalLevel), Inc, state(NewEvalLevel)) :-
    NewEvalLevel is EvalLevel + Inc.
incEvalLevel(IState, OState) :-
    incEvalLevel(IState, 1, OState).
writeEvalQuote(State) :-
    evalBackslashes(State, Backslashes),
    format('~w\'', [Backslashes]).

evalBackslashes(state(N), Backslashes) :-
    NumBackslashes is (2 ** N) - 1,
    repeatString('\\', NumBackslashes, Backslashes).

repeatString(String, Num, Result) :-
    repeatString(String, Num, '', Result).

repeatString(_, 0, Accum, Accum).
repeatString(Str, N, Accum, Result) :-
    N > 0,
    NewN is N - 1,
    string_concat(Str, Accum, Temp),
    repeatString(Str, NewN, Temp, Result).
    
ensureSuccess(Clause, _) :-
        call(Clause), !.
ensureSuccess(_, Err) :-
        throw(Err).

randomInt(X) :-
        random(0, 1000, X).

% Refers to a JavaScript number.  X is bound
% to something that can be written out.
randomNum(N) :-
    random_member(X, [nan, pinf, ninf, num]),
    numString(X, N).

randomBool(B) :-
        random(0, 2, X),
        (X == 0 -> B = true; B = false).

randomChar(X) :-
        random(97, 123, X).

randomCharCodes(0, []).
randomCharCodes(Num, [Head|Tail]) :-
        Num > 0,
        Oneless is Num - 1,
        randomChar(Head),
        randomCharCodes(Oneless, Tail).

randomString(MinLen, MaxLen, String) :-
        random(MinLen, MaxLen, Length),
        randomCharCodes(Length, Codes),
        atom_codes(String, Codes).
randomString(String) :-
        randomString(1, 100, String).

addQuotes(String, Result) :-
    string_concat('"', String, Temp),
    string_concat(Temp, '"', Result).

% TODO: this shouldn't instantiate X, but this is the easiest
% way to keep track of which variable is which
varName(X) :-
        nonvar(X).
varName(X) :-
        var(X),
        nb_getval(varcounter, Counter),
        string_concat('a', Counter, X),
        NewCounter is Counter + 1,
        nb_setval(varcounter, NewCounter).

% If var is not instantiated, then it will call clause to find something
% to instantiate Result with.  Otherwise it will simply instantiate
% the result with Var
instantiate(Var, Clause, Result) :-
        nonvar(Var) -> Result = Var ; call(Clause, Result).

mapInstantiate(Var, IfNotInstantiated, ThenApply) :-
    instantiate(Var, IfNotInstantiated, Temp),
    call(ThenApply, Temp, Result),
    write(Result).

mapInstantiate(Var, IfNotInstantiated) :-
    mapInstantiate(Var, IfNotInstantiated, =).

opString(void, 'void').
opString(typeof, 'typeof').
opString(uplus, '+').
opString(uminus, '-').
opString(bitnot, '~').
opString(lognot, '!').

opString(plus, '+').
opString(minus, '-').
opString(mul, '*').
opString(div, '/').
opString(lshift, '<<').
opString(rshift, '>>').
opString(urshift, '>>>').
opString(bitand, '&').
opString(bitor, '|').
opString(bitxor, '^').
opString(lt, '<').
opString(le, '<=').
opString(gt, '>').
opString(ge, '>=').
opString(eq, '===').
opString(ne, '!==').
opString(equiv, '==').
opString(nequiv, '!=').
opString(logand, '&&').
opString(logor, '||').
opString(in, 'in').
opString(comma, ',').
opString(instanceof, 'instanceof').

writeOp(Op) :-
        opString(Op, Str),
        write(Str).

% interleaveWrite: (Items, Writer, InputState, OutputState, Separator)
% Assumes that the writer is called like this:
% writer(Item, InputState, OutputState)
interleaveWrite([], _, State, State, _).
interleaveWrite([I], Writer, IState, OState, _) :-
    call(Writer, I, IState, OState).
interleaveWrite([I1, I2|Rest], Writer, IState, OState, Sep) :-
    call(Writer, I1, IState, TState),
    write(Sep),
    interleaveWrite([I2|Rest], Writer, TState, OState, Sep).

writeExpressions(Expressions, IState, OState, Separator) :-
    interleaveWrite(Expressions, writeExpression, IState, OState, Separator).
writeExpressions(Es, IState, OState) :-
    writeExpressions(Es, IState, OState, ', ').

writeVar(Var) :-
        varName(Var),
        write(Var).

writeVar_(Var, _, _) :-
    writeVar(Var).

writeVars(Vars, Sep) :-
        interleaveWrite(Vars, writeVar_, _, _, Sep).
writeVars(Vars) :-
        writeVars(Vars, ', ').

writeDeclBinding(binding(X, E), IState, OState) :-
        writeVar(X),
        write(' = '),
        writeExpression(E, IState, OState).
writeDeclBindings(Bindings, IState, OState) :-
        interleaveWrite(Bindings, writeDeclBinding, IState, OState, ', ').

writeObjBinding(objBinding(Name, E), IState, OState) :-
        mapInstantiate(Name, randomString),
        write(': ('),
        writeExpression(E, IState, OState),
        write(')').
writeObjBindings(Bindings, IState, OState) :-
        interleaveWrite(Bindings, writeObjBinding, IState, OState, ', ').

writePreVar(Var, Op) :-
        write(Op),
        writeVar(Var).
writePostVar(Var, Op) :-
        writeVar(Var),
        write(Op).
writePreUpd(E1, E2, Op, IState, OState) :-
        write(Op),
        write('(('),
        writeExpression(E1, IState, TState),
        write(')['),
        writeExpression(E2, TState, OState),
        write('])').
writePostUpd(E1, E2, Op, IState, OState) :-
        write('(('),
        writeExpression(E1, IState, TState),
        write(')['),
        writeExpression(E2, TState, OState),
	write('])'),
	write(Op).

% writeFunction: (Option(Name), Params, Statement, IState, OState)
writeFunction(OName, Xs, S, IState, OState) :-
        write('function '),
        (OName = some(Name) -> writeVar(Name); true),
        write('('),
        writeVars(Xs),
        write(') {'),
        writeStatement(S, IState, OState),
        write('}').

writeJump(KindName, OptionLabel) :-
        format('~a ', [KindName]),
        (OptionLabel = some(Lbl) -> writeVar(Lbl); true).

writeSwitchComponent(case(E, S), IState, OState) :-
        write('case ('),
        writeExpression(E, IState, TState),
        write('): '),
        writeStatement(S, TState, OState).
writeSwitchComponent(default(S), IState, OState) :-
        write('default: '),
        writeStatement(S, IState, OState).

writeSwitchComponents(Components, IState, OState) :-
        interleaveWrite(Components, writeSwitchComponent, IState, OState, '; ').

inDoubleRange(N) :-
    N in -1797693134862315700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000..1797693134862315700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.

% what N can be within num(N) is complex:
% -'nan' (for NaN)
% -'pinf' (for Number.POSITIVE_INFINITY)
% -'ninf' (for Number.NEGATIVE_INFINITY)
% -'num' (for some random number)
% -a number (we are provided with an actual number)
numString(A, 'NaN') :-
    % unification is unsafe here, since on an FD variable it triggers an
    % error as opposed to failure
    A == nan, !.
numString(A, 'Number.POSITIVE_INFINITY') :-
    A == pinf, !.
numString(A, 'Number.NEGATIVE_INFINITY') :-
    A == ninf, !.
numString(A, N) :-
    A == num, randomInt(N), !.
numString(N, N) :-
    number(N), !.

instantiateNum(num).

% writeExpression: Exp
writeExpression(num(N), State, State) :-
        mapInstantiate(N, instantiateNum, numString).
writeExpression(bool(B), State, State) :-
        mapInstantiate(B, randomBool).
writeExpression(str(S), State, State) :-
        mapInstantiate(S, randomString, addQuotes).
writeExpression(null, State, State) :-
        write('null').
writeExpression(this, State, State) :-
        write('this').
writeExpression(var(X), State, State) :-
        writeVar(X).
writeExpression(eval(S), IState, OState) :-
        write('eval('),
        writeEvalQuote(IState),
	incEvalLevel(IState, 1, IncState),
	writeStatement(S, IncState, TState),
	evalLevel(IState, Level),
	setEvalLevel(TState, Level, OState),
	writeEvalQuote(IState),
	write(')').
writeExpression(simpleAssign(X, E), IState, OState) :-
        writeVar(X),
        write(' = ('),
        writeExpression(E, IState, OState),
        write(')').
writeExpression(compoundAssign(X, Op, E), IState, OState) :-
        writeVar(X),
        write(' '),
        writeOp(Op),
        write('= ('),
        writeExpression(E, IState, OState),
        write(')').
writeExpression(simpleUpdate(E1, E2, E3), IState, OState) :-
        write('(('),
        writeExpression(E1, IState, TState1),
        write(')['),
        writeExpression(E2, TState1, TState2),
        write(']) = ('),
        writeExpression(E3, TState2, OState),
        write(')').
writeExpression(compoundUpdate(E1, E2, Op, E3), IState, OState) :-
        write('(('),
        writeExpression(E1, IState, TState1),
        write(')['),
        writeExpression(E2, TState1, TState2),
        write(']) '),
        writeOp(Op),
        write('= ('),
        writeExpression(E3, TState2, OState),
        write(')').
writeExpression(ternary(E1, E2, E3), IState, OState) :-
	write('('),
	writeExpression(E1, IState, TState1),
	write(') ? ('),
	writeExpression(E2, TState1, TState2),
	write(') : ('),
	writeExpression(E3, TState2, OState),
	write(')').
writeExpression(access(E1, E2), IState, OState) :-
	write('(('),
	writeExpression(E1, IState, TState),
	write(')['),
	writeExpression(E2, TState, OState),
	write('])').
writeExpression(new(E, Es), IState, OState) :-
        write('new ('),
        writeExpression(E, IState, TState),
        write(')('),
        writeExpressions(Es, TState, OState),
        write(')').
writeExpression(call(E, Es), IState, OState) :-
        write('('),
        writeExpression(E, IState, TState),
        write(')('),
        writeExpressions(Es, TState, OState),
        write(')').
writeExpression(functionExpr(OName, Xs, S), IState, OState) :-
	write('('), % in case we're in statement position
        writeFunction(OName, Xs, S, IState, OState),
	write(')').
writeExpression(binop(E1, Op, E2), IState, OState) :-
        write('('),
        writeExpression(E1, IState, TState),
        write(') '),
        writeOp(Op),
        write(' ('),
        writeExpression(E2, TState, OState),
        write(')').
writeExpression(unop(Op, E), IState, OState) :-
        writeOp(Op),
        write(' ('),
        writeExpression(E, IState, OState),
        write(')').
writeExpression(object(Bindings), IState, OState) :-
        % The outer parentheses are needed, since otherwise it can introduce
        % ambiguity between object literals and blocks containing labels
        write('({'),
        writeObjBindings(Bindings, IState, OState),
        write('})').
writeExpression(array(Es), IState, OState) :-
        write('['),
        writeExpressions(Es, IState, OState),
        write(']').
writeExpression(delete(E), IState, OState) :-
        write('delete ('),
        writeExpression(E, IState, OState),
        write(')').
writeExpression(preIncVar(X), State, State) :-
        writePreVar(X, '++').
writeExpression(preIncUpd(E1, E2), IState, OState) :-
        writePreUpd(E1, E2, '++', IState, OState).
writeExpression(postIncVar(X), State, State) :-
        writePostVar(X, '++').
writeExpression(postIncUpd(E1, E2), IState, OState) :-
        writePostUpd(E1, E2, '++', IState, OState).
writeExpression(preDecVar(X), State, State) :-
        writePreVar(X, '--').
writeExpression(preDecUpd(E1, E2), IState, OState) :-
        writePreUpd(E1, E2, '--', IState, OState).
writeExpression(postDecVar(X), State, State) :-
        writePostVar(X, '--').
writeExpression(postDecUpd(E1, E2), IState, OState) :-
        writePostUpd(E1, E2, '--', IState, OState).

writeStatement(skip, State, State) :-
        write(';').
writeStatement(seq(S1, S2), IState, OState) :-
        writeStatement(S1, IState, TState),
        write('; '),
        writeStatement(S2, TState, OState),
        write('; ').
writeStatement(E, IState, OState) :-
        writeExpression(E, IState, OState), !.
writeStatement(while(E, S), IState, OState) :-
        write('while ('),
        writeExpression(E, IState, TState),
        write(') {'),
        writeStatement(S, TState, OState),
        write('}').
writeStatement(dowhile(S, E), IState, OState) :-
        write('do {'),
        writeStatement(S, IState, TState),
        write('} while ('),
        writeExpression(E, TState, OState),
        write(');').
writeStatement(forvarin(X, E, S), IState, OState) :-
        write('for ('),
        writeVar(X),
        write(' in ('),
        writeExpression(E, IState, TState),
        write(')) {'),
        writeStatement(S, TState, OState),
        write('}').
writeStatement(forupdin(E1, E2, E3, S), IState, OState) :-
        write('for ((('),
        writeExpression(E1, IState, TState1),
        write(')['),
        writeExpression(E2, TState1, TState2),
        write(']) in ('),
        writeExpression(E3, TState2, TState3),
        write(')) {'),
        writeStatement(S, TState3, OState),
        write('}').
writeStatement(for(E1, E2, E3, S), IState, OState) :-
        write('for(('),
        writeExpression(E1, IState, TState1),
        write('); ('),
        writeExpression(E2, TState1, TState2),
        write('); ('),
        writeExpression(E3, TState2, TState3),
        write(')) {'),
        writeStatement(S, TState3, OState),
        write('}').
writeStatement(vardecl(Bindings), IState, OState) :-
        write('var '),
        writeDeclBindings(Bindings, IState, OState).
writeStatement(functionDecl(Name, Xs, S), IState, OState) :-
        writeFunction(some(Name), Xs, S, IState, OState).
writeStatement(if(E, S1, Option), IState, OState) :-
        write('if ('),
        writeExpression(E, IState, TState1),
        write(') {'),
        writeStatement(S1, TState1, TState2),
        write('}'),
        (Option = some(S2) -> 
            (write(' else {'), 
             writeStatement(S2, TState2, OState),
             write('}'));
	    (TState2 = OState)).
writeStatement(try(S1, OCatch, OFinally), IState, OState) :-
        write('try {'),
        writeStatement(S1, IState, TState1),
        write('}'),
        (OCatch = some(trybinding(X, S2)) -> 
           (write(' catch ('),
            writeVar(X),
            write(') {'),
            writeStatement(S2, TState1, TState2),
            write('}'));
	   (TState2 = TState1)),
        (OFinally = some(S3) -> 
           (write(' finally {'),
            writeStatement(S3, TState2, OState),
            write('}'));
	   (TState2 = OState)).
writeStatement(throw(E), IState, OState) :-
        write('throw ('),
        writeExpression(E, IState, OState),
        write(')').
writeStatement(labeled(Lbl, S), IState, OState) :-
        writeVar(Lbl),
        write(': {'),
        writeStatement(S, IState, OState),
        write('}').
writeStatement(break(OLbl), State, State) :-
        writeJump('break', OLbl).
writeStatement(continue(OLbl), State, State) :-
        writeJump('continue', OLbl).
writeStatement(with(E, S), IState, OState) :-
        write('with ('),
        writeExpression(E, IState, TState),
        write(') {'),
        writeStatement(S, TState, OState),
        write('}').
writeStatement(return(OE), IState, OState) :-
        write('return'),
        (OE = some(E) -> 
           (write(' ('),
            writeExpression(E, IState, OState),
            write(')'));
	   (IState = OState)).
writeStatement(switch(E, Components), IState, OState) :-
        write('switch('),
	writeExpression(E, IState, TState),
	write(') {'),
        writeSwitchComponents(Components, TState, OState),
	write('}').

writeOutStatement(S, Filename) :-
        initialState(InitState),
        open(Filename, write, Output, []),
        nb_setval(varcounter, 0),
        with_output_to(Output, 
		       ensureSuccess(writeStatement(S, InitState, _),
				     'Failed to write statement')),
        close(Output).

% the generator is a clause which takes a Statement
writeStatements(Generator, Prefix, Postfix) :-
        nb_setval(filecounter, 0),
        call(Generator, Statement),
        nb_getval(filecounter, Counter),
        string_concat(Prefix, Counter, PrefixCounter),
        string_concat(PrefixCounter, Postfix, Filename),
        writeOutStatement(Statement, Filename),
        write(Filename), nl,
        NewCounter is Counter + 1,
        nb_setval(filecounter, NewCounter),
        fail.
writeStatements(_, _, _).

% makes the AST that will handle printing.
printingHeader(try(simpleAssign(myprint, var(print)), 
                   some(trybinding(x, simpleAssign(myprint, access(var(console), str('log'))))), none)).
chainPrintHeader(seq(WithPrint, functionDecl(chainPrint, [x], seq(call(var(myprint), [var(x)]), return(some(var(x))))))) :-
    printingHeader(WithPrint).
