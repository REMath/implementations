
// pass by value and return by value of structures.

struct str {
  int a;
  int b;
};

struct cstr {
  int c;
  int d;
  cstr(const cstr &o) {
    c = 0;
    d = 0;
  }
  ~cstr() {
    c = d = 1;
  }
};

void rec_str(str s);
void rec_cstr(cstr cs);

str copy_str(str s)
{
  str os = s;
  rec_str(os);
  return os;
}

cstr copy_cstr(cstr cs)
{
  cstr ocs = cs;
  rec_cstr(ocs);
  return ocs;
}
