
// multidimensional arrays (known bounds in each direction).

void foo()
{
  int buf[100][200];
  for (int i = 0; i < 100; i++) {
    for (int j = 0; j < 200; j++)
      buf[i][j] = 0;
  }
}

