int main(int argc, char** argv) //argc = G, argv = G
{
    int a, b, c;
    a = 0;
    b = 0;
    c = taint();
    
    
    if (a < argc) {     // T(cond) = G(argc)
        b = 256;        // T(b) = U + G(argc) = G(argc)
    }
    
    c = a;              // T(c) = U !!! Shouldn't be G(argc) because the if has ended
    
    return 0;               // T(main) = U
}
 
