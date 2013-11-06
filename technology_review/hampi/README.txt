#********************************************************************
# Copyright 2008 Adam Kiezun, Vijay Ganesh
#********************************************************************
# AUTHORS: Adam Kiezun, Vijay Ganesh
#
# BEGIN DATE: October/November 2008
#
# This file belongs to the Hampi string solver project (solver for
# equations over regular expressions)
# 
# LICENSE: Please view LICENSE file in the home dir of this Program
#********************************************************************

Lead Author: Adam Kiezun

Other Contributors: Vijay Ganesh

Hampi is a solver for string constraints.  The supported constraint
language contains regular expressions and (fixed-size) context-free
grammars.  For example, you can find an 18-character string of
balanced parentheses that contains substring ")(())(", you can write a
Hampi constraint:

var v:18;
cfg S := "(" ")" | S S | "(" S ")";
reg Sbound := fix(S, 18);
assert v in Sbound;
assert v contains ")(())("; 

The first line declares the variable var of size 18 (there can be only
one variable in a Hampi constraint).  The second line declares a
context-free grammar of balanced parentheses. S is the start
nonterminal of the grammar.  The third line creates a regular language
Sbound that is the language of all 18-character strings of
well-balanced parentheses (the fix operator takes a context-free
grammar symbol, and a integer, and returns a regular-language symbol).
The fourth line asserts that the value of v is a 18-character string
of well-balanced parentheses (i.e., v is in the language L(Sbound)).
The fifth line asserts that v contains the specific substring.

STANDALONE MODE
---------------

To test Hampi, put the above constraint in a file, e.g., a.hmp, and
run 

hampi a.hmp.  

(or you can use a test input in the test directory as a template

hampi tests/hampi/tests/testSolveCFG2.hmp)

OUTPUT
--------

You should see something like this: 

{VAR(v)=(()(())()()())(())} 

which means that Hampi found the value of v that satisfies the constraints.

SERVER MODE
-----------

Hampi can also be run in a server mode - this improves solving time
for small constraints because you do not pay the cost of JVM startup.

Run the server, e.g.,
hampi_server.sh 4444

Run a query, e.g.,
hampi_client.sh 4444 a.hmp

or 

hampi_client.sh 4444 tests/hampi/tests/testSolveCFG2.hmp

To shut the server down, call

hampi_client.sh 4444 SHUTDOWN


HOW TO MEASURE IMPROVEMENT IN HAMPI PERFORMANCE 
-----------------------------------------------

1. First, translate cfg examples into Hampi examples:

   make translate-perftests

2. Create golden logs, before coding the performance improvement in Hampi:
   
   make create-perftest-gold

3. To compare the performance improvement against the golden logs:

   make run-perftests

