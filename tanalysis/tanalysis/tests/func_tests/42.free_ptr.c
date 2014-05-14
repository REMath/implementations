typedef struct {
    int a;
    int b;
} t1;

int main()
{
    t1* p;
    free((void*)p);
    return 0;
}