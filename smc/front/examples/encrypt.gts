main:
cst pg -> R0
cst pgend -> R1
cst 2863311530 -> R2
cst 1 -> R3
crypt:
load *R0 -> R4
add R2 -> R4
store R4 -> *R0
add R3 -> R0
cmp R1 >= R0
gotoLE crypt
cst pg -> R0
cst -2863311530 -> R2
decrypt:
load *R0 -> R4
add R2 -> R4
store R4 -> *R0
add R3 -> R0
cmp R1 >= R0
gotoLE decrypt
goto pg

fini:
goto main

pg:
cst 1 -> R2
cst 2 -> R3
add R3 -> R2
goto fini
pgend:

