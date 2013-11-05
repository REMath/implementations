
int main(int argc, char** argv) //argc = G, argv = G
{
    int a, b, c;
    int i, j;
    int x, y, z;
    int *p;
    a = b = 2;
    i = j = 200;
    p = &a;
    
    foo(&a);
    foo((int*) (a+b));
    foo(i + p + j);
}


void foo(int* p)
{
    int tainted = taint();
    *p = tainted;
}
