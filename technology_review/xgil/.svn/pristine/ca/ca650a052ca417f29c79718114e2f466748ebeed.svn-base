// init.c
// some tests of the initializer type-checking
// NUMERRORS 3

int a[3] = { 1,2,3 };
int b[3] = { 1,2,3,4 };           // ERROR(1)

union U { int i; float f; };
union U u = { 3 };                // ERROR(2)

struct S { int i; float f; };
struct S s = { 4, 5.6 };
struct S t = { 4, 5.6, 8 };       // ERROR(3)

