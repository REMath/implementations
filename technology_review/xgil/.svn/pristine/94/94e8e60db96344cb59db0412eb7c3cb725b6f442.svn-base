
void (*gfn)(int*, int*);

void foo(int *x, int *y)
{
  gfn(x, y);
}

void fn1(int *x, int *y) { *x = 0; }
void fn2(int *x, int *y) { *y = 0; }

void bar(int a)
{
  if (a)
    gfn = fn1;
  else
    gfn = fn2;
}
