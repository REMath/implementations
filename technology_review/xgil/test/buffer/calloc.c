
// calloc-style nonlinearity.

void* calloc(int, int);

void* wrap_calloc(int size, int count)
{
  return calloc(size, count);
}

void use_buf_calloc(int *buf, int len)
{
  for (int i = 0; i < len; i++)
    buf[i] = 0;
}

void call_calloc(int len)
{
  int *calloc_buf = wrap_calloc(sizeof(int), len);
  use_buf_calloc(calloc_buf, len);
}

void* malloc(int);

void* wrap_malloc(int size, int count)
{
  return malloc(size * count);
}

void use_buf_malloc(int *buf, int len)
{
  for (int i = 0; i < len; i++)
    buf[i] = 0;
}

void call_malloc(int len, int what)
{
  int grow = len * what;

  int *malloc_buf = wrap_malloc(sizeof(int), grow);
  use_buf_malloc(malloc_buf, grow);
}
