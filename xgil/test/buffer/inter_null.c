
void fill_buffer(char *buf, int len)
{
  int ind;
  for (ind = 0; ind < len - 1; ind++)
    buf[ind] = 1;
  buf[ind] = 0;
}

void use_buffer(char *buf)
{
  while (*buf)
    buf++;
}

void main()
{
  char buf[100];
  fill_buffer(buf, 100);
  use_buffer(buf);
}
