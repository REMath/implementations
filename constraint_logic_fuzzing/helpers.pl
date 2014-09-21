:- module(helpers, [foldl/4, nums/2]).

% foldl is apparently not defined in earlier versions of swi-pl, so here
% I define my own.
% foldl: (Clause/3, Values, BaseValue, Retval)
% The provided clause works like so: Clause(Value, Accum, Result)
foldl(_, [], Base, Base).
foldl(Clause, [Head|Tail], Accum, Retval) :-
    call(Clause, Head, Accum, NewAccum),
    foldl(Clause, Tail, NewAccum, Retval).

% Gets all the num(N)s out of an AST.  Returns the Ns.
nums(num(N), [N]) :- !.
nums(Ast, Nums) :-
    Ast =.. [_|Items],
    maplist(nums, Items, NestedNums),
    flatten(NestedNums, Nums).

