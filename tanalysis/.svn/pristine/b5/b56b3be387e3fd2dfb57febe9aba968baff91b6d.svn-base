int main(int argc, char** argv) //argc = G, argv = G
{
    int a, *b, **c;
    char *chars1, *chars2 = taint();
    a = 10;         // T(a) = U
    *b = a;         // T(b) = U
    c = b;          // T(c) = T different indirection count
    chars1 = a;     // T(chars1) = U 
    chars2 = b;     // T(chars2) = U
    return 0;
}
 