:- module(approx_evaluator, [evalExp/2,
                             anythingButNullUndefExp/1,
                             canBeCalledExp/1]).

% Basic idea: write an approximation of eval in an attempt to reduce the number
% of type errors.  Type errors we care about:
% -Attempts to update undefined, null
% -Attempts to call non-functions
% -Attempts to access undefined, null

% To this end, we want to track the following information:
% -If something is a function
% -If something is null/undefined

% Values can be one of the following:
% -nullundef, signifying definitely null or undefined
% -function, signifying definitely a function
% -object, signifying definitely a function
% -num(N), where N signifys a number, possibly NaN, pinf, ninf
% -num, where we don't know the number vale
% -bool(B), where B can be true, false
% -bool, where we don't know the boolean value
% -str(S), where S is a string
% -str, where we don't know the string's value
% -unk, signifying unknown
% -notnullundef, which represents something that's none of those

% TODO: bool, num, strings need concrete instantiations before being
% passed to evalExp

% We simply fail when a definite type error is encountered.
% This is unsound with respect to exceptions.

isNum(num(_)).
isNum(num).

isStr(str(_)).
isStr(str).

notnullundef(num(_)).
notnullundef(num).
notnullundef(bool(_)).
notnullundef(bool).
notnullundef(str(_)).
notnullundef(str).
notnullundef(function).
notnullundef(object).

anythingButNullUndef(X) :-
        notnullundef(X); X = unk.

anythingButNullUndefExp(E) :-
        anythingButNullUndef(Typ),
        evalExp(E, Typ).

join(unk, _, unk) :- !.
join(_, unk, unk) :- !.

join(nullundef, nullundef, nullundef) :- !.
join(nullundef, _, unk) :- !.
join(_, nullundef, unk) :- !.

join(num(N), num(N), num(N)) :- !.
join(num(_), num(_), num) :- !.
join(str(S), str(S), str(S)) :- !.
join(str(_), str(_), str) :- !.
join(bool(B), bool(B), bool(B)) :- !.
join(bool(_), bool(_), bool) :- !.
join(function, function, function) :- !.
join(object, object, object).
join(X, Y, notnullundef) :-
    notnullundef(X),
    notnullundef(Y), !.
join(_, _, unk).

falsy(bool(false)).
falsy(num(0)).
falsy(num(nan)).
falsy(nullundef).
falsy(str('')).

canBeCalled(function).
canBeCalled(unk).

canBeCalledExp(E) :-
        canBeCalled(Typ),
        evalExp(E, Typ).

evalArrElem(E) :-
    evalExp(E, _).

evalExp(num(N), num(N)).
evalExp(bool(B), bool(B)).
evalExp(str(S), str(S)).
evalExp(null, nullundef).
evalExp(var(_), unk).
evalExp(simpleAssign(_, E), Res) :-
        evalExp(E, Res).
evalExp(compoundAssign(_, Op, E), Res) :-
        evalExp(binop(unk, Op, E), Res).
evalExp(simpleUpdate(E1, E2, E3), Res) :-
        anythingButNullUndef(E1Res),
        evalExp(E1, E1Res),
        evalExp(E2, _),
        evalExp(E3, Res).
evalExp(compoundUpdate(E1, _,  _, _), unk) :-
        anythingButNullUndef(E1Res),
        evalExp(E1, E1Res).
evalExp(ternary(E1, E2, E3), Res) :-
        evalExp(E1, E1Res),
        (E1Res == unk ->
            (evalExp(E2, E2Res), % overapproximate both branches
             evalExp(E3, E3Res),
             join(E2Res, E3Res, Res));
            (falsy(E1Res) ->
                evalExp(E3, Res); evalExp(E2, Res))).
evalExp(access(E1, _), unk) :-
        anythingButNullUndef(E1Res),
        evalExp(E1, E1Res).
evalExp(new(E, _), object) :-
        canBeCalled(ERes),
        evalExp(E, ERes).
evalExp(call(E, _), unk) :-
        canBeCalled(ERes),
        evalExp(E, ERes).
evalExp(functionExpr(_, _, _), function).
evalExp(binop(_, _, _), unk).
evalExp(unop(_, _), unk).
evalExp(object(_), object).
evalExp(array(_), array).
%skipping 'this' because we currently don't emit it
evalExp(delete(E), bool) :-
        anythingButNullUndef(ETyp),
        evalExp(E, ETyp).
% without some refactoring this is kind of not going to be able to be any more precise as-is.
% the difficulty arises because null++ doesn't work, but undefined++ does, and this evaluator
% conflates null and undef.
evalExp(eval(_), unk).
evalExp(PrePostIncDec, unk) :-
        prePostIncDec(PrePostIncDec).

% TODO: copy/pase from approx_eval.pl
prePostIncDec(preIncVar(_)).
prePostIncDec(preIncUpd(_, _)).
prePostIncDec(postIncVar(_)).
prePostIncDec(postIncUpd(_, _)).
prePostIncDec(preDecVar(_)).
prePostIncDec(preDecUpd(_, _)).
prePostIncDec(postDecVar(_)).
prePostIncDec(postDecUpd(_, _)).
