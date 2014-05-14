int main(int argc, char** argv)
{
    int x = foo (10);
    int y = foo2 (20);
    return 0;
} 

int foo(int n) 
{
    int r = taint();
    if (n > 1)
        r = n * foo(n);
    else 
        r = 1;
    return r;
}

int foo2(int n)
{
    int r = taint(), tainted = taint();
    if (n > 1)
        r = n * foo2(n);
    else 
        r = tainted;
    return r;
}
