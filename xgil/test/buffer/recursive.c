
// recursive function calls. these currently aren't handled soundly.

void access(int *buf, int n)
{
  for (int i = 0; i < n; i++)
    buf[i] = 0;
  if (n > 10)
    access(buf + 10, n - 10);
}

void call_access()
{
  int buf[100];
  access(buf, 100);
}

void bad_access(int *buf, int n, int flag)
{
  for (int i = 0; i < n; i++)
    buf[i] = 0;
  bad_access(buf + 10, n);
}

void call_bad_access()
{
  int buf[100];
  bad_access(buf, 100);
}



