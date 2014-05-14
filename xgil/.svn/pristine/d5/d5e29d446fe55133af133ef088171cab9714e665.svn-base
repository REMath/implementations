
struct str {
  int x;
  str() : x(0) {}
  str(int _x) : x(_x) {}
  // str(const str &o) : x(o.x) {}
  void set_x(int v) { x = v; }
  ~str() { x = 1; }
};

void bar(str xs);

void foo()
{
  bar(str());
  str s = str();
  // s = str();
  // s.set_x(2);
}
