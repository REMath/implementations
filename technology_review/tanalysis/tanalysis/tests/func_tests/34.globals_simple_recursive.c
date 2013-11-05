int prod = 1;
int prod2 = 1;

int main(int argc1, int argc2)
{
    int tainted = taint();
    int n = 100;
    prod = argc1;
    prod2 = argc1;
    foo(argc2);
    bar(argc2);
    return 0;
}


void foo(int n)
{
    prod *= n;
}


void bar(int n)
{
    if (n == 0)
        return;
    else {
        prod2 *= n;
        bar(n-1);
    }
}

