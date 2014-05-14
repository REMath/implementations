
int foo()
{
  const int &x = 3;
}

struct str { int x; };

void extern_int(const int&);
void extern_str(const str&);
void extern_str_val(str);

int baz()
{
  extern_int(3);
  extern_str(str());
  extern_str_val(str());
}

