
int main(int argc, char** argv) //argc = G, argv = G
{
    int a, b, c;
    int i, j;
    int x, y, z;
    int *p;
    a = b = 2;
    i = j = 200;
    p = &b;
    
    x = foo(&a);
    y = foo((int*) (a+b));
    z = foo(i + p + j);
    return 0;
}


int foo(int* p)
{
    int tainted = taint();
    *p = tainted;
    return 100;
}
