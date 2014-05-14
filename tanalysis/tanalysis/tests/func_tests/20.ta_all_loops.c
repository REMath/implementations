int main(int argc, int argc2, char** argv) //argc = G, argv = G
{
    int a, b, c, d, tainted, i;
    int a1, b1, c1, d1, i1;
    a = b = d = 0;
    c = tainted = taint();
    for (i = 0; i < argc; ++ i) {
        a++;
        while (b < 500) {
            do {
                c = argc + 1;
            } while (c < argc);
        }
        b+=tainted;
    }
                                    // T(a) = G(argc)
                                    // T(b) = T
                                    // T(c) = T
                                    // T(i) = G(argc)
    
    a1 = b1 = c1 = d1 = 0;
    for (i1 = 0; i1 < argc; ++ i1) {
        a1++;
        while (b1 < 500) {
            do {
                c1 = argc + 1;
            } while (c1 < argc); 
        }
        b1+=2;
    }
                                    // T(a1) = G(argc)
                                    // T(b1) = G(argc)
                                    // T(c1) = G(argc)
    
    return 0;
}
 
 