
void* malloc(int);

void foo(void ***buf)
{
  *buf = (void**) malloc(4);
}

void bar()
{
  void **buf;
  foo(&buf);
  void *use_buf = buf[0];
  use_buf[0] = 0;
}
