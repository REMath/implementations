
// inserting null terminator example, from Area::ParseCoords

char* strchr(char*, char);
int atoi(char*);

int is_space(char c)
{
  return c == ' ' || c == '\n' || c == '\t';
}

void counter(int *list, int *count, char *buf)
{
  char *tbuf = buf;
  for (int i = 0; i < count; i++) {
    char *xbuf;

    xbuf = strchr(tbuf, ',');
    if (xbuf)
      *xbuf = '\0';

    while (is_space(*tbuf))
      tbuf++;

    while (*tbuf == ' ')
      tbuf++;

    if (*tbuf == '\0')
      list[i] = 0;
    else
      list[i] = atoi(tbuf);

    if (xbuf) {
      *xbuf = ',';
      tbuf = xbuf + 1;
    }
  }
}

void call_counter()
{
  int list[20];
  counter(list, 20, "fubarbaz");
}
