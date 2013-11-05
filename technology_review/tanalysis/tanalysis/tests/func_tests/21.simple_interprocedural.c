int global;

int main(int argc, char** argv) //argc = G, argv = G
{
    int a = 2;
    int b = 2;
    int c = foo (a, b);
    return 0;
}

int foo(int x, int y)
{
    return x + y;
}
 
 