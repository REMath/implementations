int main(int argc, char** argv) //argc = G, argv = G
{
    int b, c;       
    b = c = taint();// all T
    if (1)          // T(cond) = U
        b = 3;      // T(b) = U + U = U
    else 
        c = 4;      // T(c) = U + U = U
                    // T(b) = U + T = T !!! but actually what happens here is
                    // that cil removes the false branch because of the constant
                    // condition so that T(b) becomes U
                    // T(c) = T + U = T !!! => T(c) = T
    return b + c;   // T(main) = T 
}