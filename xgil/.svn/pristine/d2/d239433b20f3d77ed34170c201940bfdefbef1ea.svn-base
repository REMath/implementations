
void* memcpy(void*, void*, unsigned long);

void use_buf(char *buf)
{
  while (*buf)
    buf++;
}

void fill_buf(char *buf, int pos)
{
  buf[pos] = 0;
}

void use_memcpy()
{
  char src[100];
  char tgt[100];

  fill_buf(src, 99);
  memcpy(tgt, src, 100);
  use_buf(tgt);
}

void use_memset()
{
  char tgt[100];

  memset(tgt, 0, sizeof(tgt));
  use_buf(tgt);
}
