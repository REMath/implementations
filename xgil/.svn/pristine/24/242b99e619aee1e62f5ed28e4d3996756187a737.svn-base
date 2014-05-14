
// non-zeroing allocator.
void* malloc(int);

// zeroing allocator.
void* calloc(int, int);

void call_malloc()
{
  char *buf = malloc(100);

  while (*buf)
    buf++;
}

void call_calloc()
{
  char *buf = calloc(100, 1);

  while (*buf)
    buf++;
}

struct str
{
  char *field;
};

void call_uninit()
{
  struct str *s = malloc(sizeof(struct str));
  char *buf = s->field;

  while (*buf)
    buf++;
}
