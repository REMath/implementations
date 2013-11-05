#include <stdio.h>

int main(int argc)
{
    int a = 2;
    int b = 3;
    while (argc < 10) {
        foo(b);
        b = taint();
    }
}

void foo(int x)
{
    char* buf;
    buf[x] = 22;
}

