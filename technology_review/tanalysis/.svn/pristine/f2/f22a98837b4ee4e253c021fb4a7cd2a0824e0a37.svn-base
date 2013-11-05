void main(int argc) //argc = G, argv = G
{
    int b = argc;
    int a = taint ();
    int x;
    if (argc) {
        x = taint();
    } else {
        x = 222;
    }
    foo(a);
    foo(b); 
}

int foo(int n)
{
    int x;
    if (n) {
        x = 2;
        return n * foo(n - 1);
    } else {
        x = taint();
        return 1;
    }
}
 
