int global = 2;

int main()
{
    foo();
    untaint_global();
    return 0;
}

void foo()
{
    int tainted = taint();
    global = tainted;
}

void untaint_global()
{
    global = 100;
}
