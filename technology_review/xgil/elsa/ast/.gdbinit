# .gdbinit   -*- sh -*-

#file ccsstr
#file agrampar
file astgen
break main
break breaker
set args example.ast
set print static-members off
#set args ast.ast
#set args ../parsgen/gramast.ast
run
