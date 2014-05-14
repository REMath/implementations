int main(int argc, char** argv)
{
    int x = foo (10, 10);
    int p1 = taint();
    int p2 = taint();
    int y = foo (foo_iterative(p1), p2);
    int tainted = taint();
    int z = foo (tainted, 100);
    int t = foo_iterative(z);
    int q = foo (foo_iterative(tainted), tainted);
    int p = foo (100, tainted);
    
    return 0;
}

int foo_iterative(int n)
{
    int prev;
    int prev_prev;
    int i;
    int aux = taint();
    
    prev = 1;
    prev_prev = 1;
    
    if (n < 1)
        return 0;
    for (i = 2; i <= n; ++ i) {
        aux = prev + prev_prev;
        prev = prev_prev;
        prev_prev = aux;
    }
    return prev_prev;
}

int foo(int n, int x) 
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
    if (n > 1)
        r = n * foo(n, 100);
    else 
        r = 1;
    return r;
} 
