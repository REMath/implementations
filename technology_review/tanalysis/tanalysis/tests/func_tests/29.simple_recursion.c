int main(int argc, char** argv)
{
    int x = foo (10);
    int y = foo (argc);
    int tainted = taint();
    int z = foo (tainted);
    return 0;
}

int foo(int n) 
{
    int r = taint();
    if (n > 1)
        r = n * bar(n);
    else 
        r = 1;
    return r;
}

int bar(int n)
{
    int r = taint();
    int tainted = taint();
    if (n > 1)
        r = n * foo(n);
    else 
        r = tainted;
    return r;
} 
