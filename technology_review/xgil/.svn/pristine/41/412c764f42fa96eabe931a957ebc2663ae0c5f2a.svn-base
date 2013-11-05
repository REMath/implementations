
void simple(int x)
{
  // x++;
  while (x);
}

struct str { int a; };

void test_while(int x, int y, int z)
{
  while (x) {
    str s;
    if (y)
      continue;
    if (z)
      break;
    x++;
  }
}

void test_dowhile(int x, int y, int z)
{
  do {
    str s;
    if (y)
      continue;
    if (z)
      break;
    x++;
  } while (x);
}

void test_for(int y, int z)
{
  for (int i = 0; i < 100; i++) {
    str s;
    if (y)
      continue;
    if (z)
      break;
  }
}
