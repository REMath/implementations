int main(int argc, char** argv) //argc = G, argv = G
{
    int a, b, d, e;         
    a = b = d = e = taint();// all tainted
    a = 2;                  //should be untainted
    b = argc;               //T(b) = G(argc)
    d = a + b + d;          //T(d) = U + G(argc) + T = T
    e = a + b + b;          //T(d) = U + G(argc) + G(argc) = G(argc)
    return 0;               // T(main) = U 
}