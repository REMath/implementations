
template<typename N>
struct local_array
{
  // int buf[N * 2 + 3];
  int buf[2];
  N a;

  int get() { return buf[0]; }
  int get(int n) { return buf[n]; }
};

int foo()
{
  local_array<int> buf;
  return buf.get() + buf.get(1);
}
