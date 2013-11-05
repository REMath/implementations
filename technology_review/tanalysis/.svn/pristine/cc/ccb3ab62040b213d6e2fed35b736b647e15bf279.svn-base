int main()
{
    int a = taint(), b;
    
    b = 200;
    if (b) {
        if (a) {
            a = b = 10;
            a*= b;
        } else {
            a = 500;
        }
    }
    return a;
}