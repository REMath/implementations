int main(int argc, char** argv) //argc = G, argv = G
{
    int a, b, c;
    int a1, b1, c1;
    int a2, b2, c2;
    a = c = 0;
    b = taint();
    a1 = b1 = c1 = 0;
    a2 = b2 = c2 = 0;
    
    while (a < 10) {                // T(cond) = U
        while (b < 10) {            // T(cond) = T
            while (c < argc) {      // T(cond) = G(argc)
                c++;                // T(c) = U + G(argc) + T
            }
            b++;                    // T(b) = T
        } 
        a++;                        // T(a) = U
    }
    
    while (a1 < 10) {               // T(cond) = U
        while (b1 < argc) {         // T(cond) = G(argc)
            while (c1 < 10) {       // T(cond) = U
                c1++;               // T(c1) = U + G(argc) + U = G(argc)
            }
            b1++;                   // T(b1) = G(argc)
        }
        a1++;                       // T(a1) = U
    }
    
    while (a2 < 10) {
        while (b2 < argc) {
            while (c2 < 10) {   
                c2++;
            }
            b2++;
        }
        a2 = b;                     // !!!! a2 becomes tainted -> first cond becomes
                                    // tainted -> b2 and c2 become tainted
    }
    
    return 0;               // T(main) = U
}
 
