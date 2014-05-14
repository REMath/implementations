int main(int argc, char** argv) //argc = G, argv = G
{
    int a2, b, b2;
    a2 = b2 = 2;                    // T(a2) = T(b2) = U
    b = taint();                    // T(b) = T
    while (a2 < 10) {
        while (b2 < argc) {
            b2 = 1;
        }
        a2 = b;                     // !!!! a2 becomes tainted -> first cond becomes
                                    // tainted -> b2 becomes tainted
    }
}
 
