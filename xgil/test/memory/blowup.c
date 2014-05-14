
int fubar();

void blowup(int x)
{
  if (x == 1)
    x = fubar();
  if (x == 2)
    x = fubar();
  if (x == 3)
    x = fubar();
  if (x == 4)
    x = fubar();
  /*
  if (x == 5)
    x = fubar();
  if (x == 6)
    x = fubar();
  if (x == 7)
    x = fubar();
  if (x == 8)
    x = fubar();
  if (x == 9)
    x = fubar();
  if (x == 10)
    x = fubar();
  if (x == 11)
    x = fubar();
  if (x == 12)
    x = fubar();
  if (x == 13)
    x = fubar();
  */
}


