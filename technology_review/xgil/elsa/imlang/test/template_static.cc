
// template classes with static variables?
// gcc doesn't like this.

template <class T>
class Fubar
{
 public:
  static T buf[];
};

int Fubar<int>::buf[10];

int foo()
{
  return Fubar<int>::buf[0];
}
