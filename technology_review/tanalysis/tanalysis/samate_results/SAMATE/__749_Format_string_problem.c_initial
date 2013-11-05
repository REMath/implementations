/* The following example is exploitable, due to the printf() call in the printWrapper()
function. Note: The stack buffer was added to make exploitation more
simple.
*/
#include <stdio.h>
#include <string.h>
void printWrapper(char *string) {
printf(string);
}

int main(int argc, char **argv) {
char buf[5012];
memcpy(buf, argv[1], 5012);
printWrapper(argv[1]);
return (0);
}


