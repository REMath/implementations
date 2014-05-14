int main(int argc, char** argv) //argc = G, argv = G
{
    int a, b;
    int a1, b1;
    a = b = 0;              // T(a) = T(b) = U
    a1 = b1 = taint();      // T(a1) = T(b1) = T
    
while (a < 10) {            // T(cond) = U
        while (b < 20) {    // T(cond) = U + U = U
            b++;            // T(b) = U
        }
        a++;                // T(a) = U
    } 
    
    a1 = 0;                 // T(a1) = U
    while (a1 < 10) {       // T(cond) = U
        while (b1 < argc) { // T(cond) = U + G(argc) + T = T
            b1++;           // T(b1) = T
        }
        a1++;               // T(a1) = U
    }
    
    return 0;               // T(main) = U
                            // T(a) = T(b) = T(a1) = U
                            // T(b1) = T
}
 
