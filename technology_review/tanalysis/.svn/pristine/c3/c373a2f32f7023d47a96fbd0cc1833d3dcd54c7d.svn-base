int main(int argc, char** argv) //argc = G, argv = G
{
    int *p, a, *q, b, c;
    p = taint();
    c = taint();
        
    a = 2;
    p = &a;
    b = *p;
    *q = c;

    return 0;
}
 