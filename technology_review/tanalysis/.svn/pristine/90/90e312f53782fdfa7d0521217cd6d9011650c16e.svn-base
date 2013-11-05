int main(int argc) {
    int a[234];
    int* b;
    int* c;
    int* d;
    int tainted = taint();
    b = taint();
    a[2] = 2;
    a[tainted] = 354;
    c[argc] = 23;
    d[345] = argc;
    return 0;
}