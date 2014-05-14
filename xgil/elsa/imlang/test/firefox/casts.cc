
void foo(int *n);

void bar()
{
  foo(((void*) 0));
}

