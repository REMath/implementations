
struct str {
  int x;
  str() { x = 1; }
  int add_x(int y) { return x + y; }
  int& get_x() { return x; }
  void get_x_arg(int &v) { v = x; }

  static int return_three() { return 3; }

  void (**fn)();

};

void foo(int y)
{
  str s;
  // s = str();
  (*******s.fn)();
  int v = s.add_x(y);
  int w = s.get_x();
  int &t = s.get_x();

  int u;
  s.get_x_arg(u);

  int a = str::return_three();
  int b = s.return_three();
}
