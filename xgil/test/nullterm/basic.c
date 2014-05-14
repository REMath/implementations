
char add_these(char a, char b)
{
  return a + b;
}

int scan_buffer(char *buf, char tgt)
{
  // char newval = add_these(tgt, 'a');
  char newval = 'c';

  while (*buf) {
    if (*buf == newval)
      return 1;
    buf++;
  }

  if (*buf == tgt)
    buf++;
  return *buf;
}

void main()
{
  scan_buffer("fubar", 'x');
  // scan_buffer(" fubar! ",'x');
  // scan_buffer("",'x');
}

/*
void main2()
{
  char not_terminated[20];
  scan_buffer(not_terminated, 'x');
}
*/
