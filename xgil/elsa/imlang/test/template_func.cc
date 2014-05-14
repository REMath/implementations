
// templates functions.

template <class T>
T add_these_two(T v0, T v1)
{
  return v0 + v1;
}

int foo_int(int x, int y)
{
  return add_these_two<int>(x, y);
}

double foo_double(double x, double y)
{
  return add_these_two<double>(x, y);
}
