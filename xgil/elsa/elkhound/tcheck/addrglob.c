// addrglob.c
// NUMERRORS 2
// verify addr-of-global restrictions

int x;    // fine

int foo()
{
  return x;
}


int y;

int bar()
{
  int z = 3;
  {
    int *p = &y;   // ERROR(1)
    z = *p;        // ERROR(1)
  }
  return z;
}


int q thmprv_attr(addrtaken);

int *zoo()
{
  return &q;
}
   

int ug thmprv_attr(misspelled);     // ERROR(2)

