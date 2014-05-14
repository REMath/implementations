
struct JSContext;
struct JSObject { int f; };

void js_GC() {}

namespace js {

template <typename T>
class AutoRooter {
public:
  AutoRooter(JSContext *cx, T **ptr) : ptr(ptr) {}
  ~AutoRooter() {}

  T **ptr;
};

template <typename T>
class AutoRooterVar {
  public:
    AutoRooterVar(JSContext *cx, T *value)
        : ptr(value), root(cx, &ptr)
    {}

    operator T * () { return ptr; }
    T * operator ->() { return ptr; }
    T *& operator =(T *value) { ptr = value; return ptr; }
    T ** addr() { return &ptr; }

  private:
    T *ptr;
    AutoRooter<T> root;
};

}
