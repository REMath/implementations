typedef struct {
    int a;
    char c1;
    char c2;
    char c3;
    char c4;
} t1;

typedef struct {
    int a;
    int b;
    int c;
} t4;

typedef struct {
    int a;
    int b;
} t2;

int main(int argc, char** argv) //argc = G, argv = G
{
    t1* s1;
    t2 s2;
    t4* s4;
    s2.a = 10;
    s2.b = 10;
    s1 = (t1*)(&s2);        // T(s1) = U
    s4 = (t4*)(&s2);        // T(s4) = T
    return 0;   
}
 