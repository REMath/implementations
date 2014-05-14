
struct str { int a; int b; };

void foo()
{
  int x = __builtin_types_compatible_p(int, str);
  int y = __is_pod(int);
  int z = __has_trivial_copy(str);
}


