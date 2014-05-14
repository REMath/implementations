int main()
{
    int a, b;         
    a = 2;            // T(a) = U
    b = taint();      // T(b) = T
    while (a < 10)    // T(cond) = U
        a = a + b;    // T(a) = U + T = T  
    return 0;         // T(main) = U
}
 
