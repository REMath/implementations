int global1;
int global2;

int main(int argc)
{
    int a, b, c, x, y;
    int z, t;         
    a = 2;            // T(a) = U
    b = argc;         // T(b) = T
    c = 33;           // T(c) = U  
    
    x = foo(a, b);    // T(x) = T
    y = foo(a, c);    // T(y) = U
    z = foo_rec(a);   // T(z) = U
    t = foo_rec(b);   // T(t) = T
    
    foo_global1(1000);// T(global1) = U
    foo_global2(b);   // T(global2) = T
    return 0;         // T(main) = U
}
 
 
int foo(int x, int y)
{
    return x + y;
} 

int foo_rec (int n)
{
    if (n == 0)
        return 1;
    else
        return n * foo_rec(n-1);
}

void foo_global1 (int n)
{
    if (n != 0) {
        global1 *= n;
        foo_global1(n-1);
    }
}

void foo_global2 (int n)
{
    if (n != 0) {
        global2 *= n;
        foo_global2(n-1);
    }
}
