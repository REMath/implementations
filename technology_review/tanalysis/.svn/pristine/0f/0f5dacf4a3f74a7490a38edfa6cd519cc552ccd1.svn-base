int main(int argc, int argc2, char** argv) //argc = G, argv = G
{
    int a, b, c;                    
    a = b = c = taint();            // T(all) = T
    if (argc) {                     // T(cond) = G(argc)
        c = 3;                      // T(c) = U + G(argc) = G(argc)
    } else {
        c = argc2;                  // T(c) = G(argc2) + G(argc)
    }
                                    // JOIN: 
                                    //       T(c) = G(argc2) + G(argc) 
    return c;                       // T(main) = G(argc2) + G(argc)
}
