int main(int argc, char** argv) //argc = G, argv = G
{
    unsigned int a, b, c, d, e, f, g; 
    a = b = c = d = e = f = g = taint();// all T
    a = sizeof(int);     // T(a) = U
    b = sizeof(a+c);     // T(b) = T
    c = sizeof(b);       // T(c) = T
    d = sizeof(a*a);     // T(d) = U
    e = __alignof__(int);// T(e) = U 
    f = __alignof__ (a); // T(f) = U
    g = __alignof__ (b); // T(g) = U
    return a + b + c + d + e + f + g; // T(main) = T
}