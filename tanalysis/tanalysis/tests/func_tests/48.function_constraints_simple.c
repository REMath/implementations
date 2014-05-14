void strcpy_1(char* dest, char* source)
{
    dest = source;
}

int main()
{
    char* src;
    char* dst;
    
    dst = taint();
    src = 0;
    strcpy(dst, src); // dest tainted => operation allowed
    strcpy(dst, src); // dest untainted + src untainted => operation allowed
    src = taint ();
    strcpy(dst, src); // dest untainted + src tainted => operation not allowed
    
}