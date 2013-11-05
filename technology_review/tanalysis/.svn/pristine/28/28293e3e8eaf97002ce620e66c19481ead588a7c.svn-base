int main(int argc, char** argv) //argc = G, argv = G
{
    int a = taint(), c = taint();
    char b;
    c = 0;                          // T(c) = U
    a = (int)((unsigned int) c);    // T(a) = U        
    b = (int)((char)c);             // T(b) = T
    return 0;
}
 