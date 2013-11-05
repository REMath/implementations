#include <stdio.h>

int main()
{
    int a = 2;
    int b = taint();
    int c = 33;
    
    printf ("%d\n", a + c);
    foo(b);
    foo(2);    
    return 0;
}

void foo(int x)
{
    char* buf;
    buf[x] = 22;
}

