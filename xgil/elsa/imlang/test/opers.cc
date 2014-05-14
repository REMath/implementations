
// operation testing.

int foo(int x, int &y)
{
  // gcc rejects this but not elsa and it crashes our code.
  // int &z = x + y;

  int z = x + y;
  // z++;
  int iz = z++;
  z += 2;
  int pz = z += 2;
}



