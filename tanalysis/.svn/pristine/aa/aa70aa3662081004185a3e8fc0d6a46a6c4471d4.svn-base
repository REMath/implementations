int main(int argc, int argc2, char** argv) //argc = G, argv = G
{
            int a, b, c;                    
            a = b = c = taint();            // T(all) = T
/* 2: */    if (argc) {                     // T(cond) = G(argc)
    
/* 4: */        if (2) {                    // T(cond) = U
/* 5: */            b = 2;                  // T(b) = U
                    c = 3;                  // T(c) = U
                } else {
/* 6: */            c = 2;                  // T(c) = U
                }
                                            // JOIN: T(b) = U + T + U = T
                                            //       T(c) = U + U + U = U
                
            } else {
/* 7: */        c = argc2;                  // T(c) = G(argc2)
            }
                                            // JOIN: T(b) = T + T + G(argc) = T
                                            //       T(c) = U + G(argc2) + G(argc) = G(argc2) + G(argc)
/* 8: */    return c;                       // T(main) = G(argc2) + G(argc)
}
 
