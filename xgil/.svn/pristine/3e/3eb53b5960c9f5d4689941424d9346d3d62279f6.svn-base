
class Foo {
public:
  // should not generate anything in output without seeing
  // the actual definition, same as global variables.
  static int buf0[];
  static int buf1[];

  static int x;

  // this is OK.
  static const int y = 5;

  void foo()
  {
    // this is OK too.
    static int z;
  }
};

int Foo::buf1[] = { 1, 2, 3, 4, 5 };
