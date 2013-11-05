int main(int argc, char** argv) 
{
    int x = bar(0, 1, 2);
    int y = bar(0, 1, argc);
    return 0;
}

int foo(int x3) 
{
    return 10;
}

int bar(int x1, int y1, int z1) 
{
    return x1 + foobar(z1, x1, y1);
}

int foobar(int x2, int y2, int z2)
{
    return x2 + foo(y2);
}
 