
// templates classes.

class BaseArray
{
  int junk;
};

template <class T>
class Array : public BaseArray
{
 public:
  T m_array[20];
  int m_count;

  Array<T>() : m_count(0) {}

  T& get(int ind) {
    return m_array[ind];
  }

  template <class T>
  void get(T *v) {}
};

struct str
{
  int a;
  int b;
};

int foo_int()
{
  Array<int> arr;
  return arr.get(5);
}

int foo_str()
{
  Array<str> arr;
  return arr.get(5).a;
}
