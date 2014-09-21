:- module('evaluation', [doEvaluation/5, genAstsFor/3]).

% Gathers data for the evaluation.  This means specifically we want
% the following for a given time quantum:
% 1.) Total number of stochastic ASTs generated
% 2.) Total number of unique stochastic ASTs generated
% 3.) Total number of unique and interesting (CLP-accepted) ASTs generated
% 4.) Total number of unique and interesting CLP-generated ASTs

% -Generator
% -List of ASTs
% -Start time, in seconds
% -How long, in seconds
genAstsFor(Generator, Asts, Start, Secs) :-
	statistics(real_time, [Total, _]),
	Temp is Total - Start,
	(Temp >= Secs -> Asts = [];
	    (((call(Generator, Ast), !) ->
		Asts = [Ast|Rest];
		Asts = Rest),
	     genAstsFor(Generator, Rest, Start, Secs))).

% -Generator
% -List of ASTs
% -How long, in seconds
genAstsFor(Generator, Asts, Secs) :-
	statistics(real_time, [Start, _]),
	genAstsFor(Generator, Asts, Start, Secs).

% ISSUE: the stochastic predicate should be repeatedly queried, whereas
% the CLP predicate should be treated nondeterministically
genAstsNondeterFor(Generator, NumAsts, Secs) :-
    nb_setval(nondeterasts, 0),
	statistics(real_time, [Start, _]),
	%format('ABOUT TO CALL ~w~n', [Generator]),
	call(Generator, _),
	%writeln(Ast),
	nb_getval(nondeterasts, OldNum),
	NewNum is OldNum + 1,
	nb_setval(nondeterasts, NewNum),
	statistics(real_time, [Total, _]),
	Temp is Total - Start,
	(Temp >= Secs -> 
	    (NumAsts = NewNum,
	     !, true);
	    false), !.

genAstsNondeterFor(_, Num, _) :-
   nb_getval(nondeterasts, Num).

% doEvaluation: StochasticPredicate, CLPPredicate, AreEqual, Result
% -StochasticPredicate is a clause that takes a statement and will bind it to something.
%  It is assumed to behave in a random, deterministic fashion.
% -CLPPredicate is a clause that takes a statement and will bind it to something / check.
%  It is assymed to behave in a nondeterministic fashion
% -MakeUnique - returns a list of unique ASTs
% -NumberOfS
% -Result - result(Point1, Point2, Point3, Point4)
doEvaluation(StochasticPredicate, CLPPredicate, MakeUnique, Secs, result(TotalSto, UniqueSto, InterestingSto, TotalCLP)) :-
	%format('STOCHASTIC~n'),
	genAstsFor(StochasticPredicate, StoAsts, Secs), !,
	%format('MAKING UNIQUE~n'),
	call(MakeUnique, StoAsts, UniqueStoAsts), !,
	include(CLPPredicate, UniqueStoAsts, InterestingUniqueStoAsts), !,
	%format('CLP~n'),
	genAstsNondeterFor(CLPPredicate, TotalCLP, Secs), !,
	%format('CLP DONE~n'),
	length(StoAsts, TotalSto),
	length(UniqueStoAsts, UniqueSto),
	length(InterestingUniqueStoAsts, InterestingSto).

% This is for measuring everything that doEvaluation does, except for
% The generation rate of the CLP predicate.
doEvaluationUber(StochasticPredicate, CLPPredicate, MakeUnique, Secs, result(TotalSto, UniqueSto, InterestingSto)) :-
	format('STOCHASTIC~n'),
	genAstsFor(StochasticPredicate, StoAsts, Secs), !,
	format('MAKING UNIQUE~n'),
	call(MakeUnique, StoAsts, UniqueStoAsts), !,
	include(CLPPredicate, UniqueStoAsts, InterestingUniqueStoAsts),
	length(StoAsts, TotalSto),
	length(UniqueStoAsts, UniqueSto),
	length(InterestingUniqueStoAsts, InterestingSto).
