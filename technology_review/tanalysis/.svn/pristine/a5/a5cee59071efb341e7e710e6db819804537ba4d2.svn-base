int main(int argc, char** argv) //argc = G, argv = G
{
    int b, c;    
    b = c = taint();// all T
    if (argc) {     // T(cond) = U
        b = 3;      // T(b) = U + G(argc) = G(argc)
        c = argc;   // T(c) = G(argc) + G(argc) = G(argc)
    } else { 
        c = 4;      // T(c) = U + G(argc) = G(argc)
    }
                    // join:
                    // T(b) = G(argc) + T = T 
                    // T(c) = G(argc) + G(argc) = G(argc) 
    return b + c;   // T(main) = T 
}