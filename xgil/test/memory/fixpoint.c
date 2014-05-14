
void foo(int *x, int *y)
{
  *x = 0;
  if (x != y)
    foo(y, y);
}
