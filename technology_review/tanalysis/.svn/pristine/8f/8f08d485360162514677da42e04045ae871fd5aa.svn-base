
int main(int argc, char** argv) 
{
    int tainted = taint();
    int result_test = 1;
    int result_tainted = 1;
    int result_generic = 1;
    int result_generic2 = argc; 
    factorial(&result_test, 100);
    factorial(&result_tainted, tainted);
    factorial(&result_generic, argc);
    factorial(&result_generic2, 1000);
    return 0;
} 


void factorial(int *result, int n)
{
    if (n == 0)
        return;
    *result = *result * n;
    factorial (result, n - 1);
}