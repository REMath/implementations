

template<int N>
inline bool greater_ten(const char (&str)[N], int c)
{
  return N >= c;
}

void foo()
{
  bool b0 = greater_ten("fubar", 5);
}
