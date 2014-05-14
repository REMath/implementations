
typedef struct str {
  int *buf;
  int len;
} str;

void foo(str *s)
{
  s->buf[s->len] = 0;
}

str *glob;

void bar()
{
  glob->buf[glob->len] = 0;
}

void* malloc(int len);

void baz(int len)
{
  glob->buf = malloc(len * sizeof(int));
  glob->len = len;

  foo(glob);
  bar();
}
