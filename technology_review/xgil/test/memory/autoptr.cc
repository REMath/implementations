
// from firefox. I have no idea why this is supposed to compile. thanks C++.
// whatever, the Elsa AST is busted.

template <class T>
class nsAutoPtr
  {
    private:

      class Ptr
        {
          public:
            Ptr( T* aPtr )
                  : mPtr(aPtr)
              {
              }

            operator T*() const
              {
                return mPtr;
              }

          private:
            T* mPtr;
        };

    private:
      T* mRawPtr;

    public:
      typedef T element_type;

     ~nsAutoPtr()
        {
          delete mRawPtr;
        }



      nsAutoPtr()
            : mRawPtr(0)

        {
        }

      nsAutoPtr( Ptr aRawPtr )
            : mRawPtr(aRawPtr)

        {
        }


      T*
      get() const
        {
          return mRawPtr;
        }

      operator T*() const
        {
          return get();
        }

      T*
      operator->() const
        {
          return get();
        }

    public:
      T&
      operator*() const
        {
          return *get();
        }
  };

void use_auto_ptr()
{
  nsAutoPtr<int> fubar(new int[100]);
  fubar[99] = 0;
}
