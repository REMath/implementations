// exception.h
// implementation of exception.h, no namespaces

#ifndef __EXCEPTION_H
#define __EXCEPTION_H

// contents taken from C++ standard, section 18.6

//namespace std {
  class exception;
  class bad_exception;

  typedef void (*unexpected_handler)();
  unexpected_handler set_unexpected(unexpected_handler f) throw();
  void unexpected();

  typedef void (*terminate_handler)();
  terminate_handler set_terminate(terminate_handler f) throw();
  void terminate();

  bool uncaught_exception();
//}

//namespace std {
  class exception {
    // sm: presumably a real implementation would have something
    // in here, but for now my only interest is with parsing
  public:
    exception() throw();
    exception(const exception&) throw();
    exception& operator=(const exception&) throw();
    virtual ~exception() throw();
    virtual const char* what() const throw();
  };
//}

//namespace std {
  class bad_exception : public exception {
  public:
    bad_exception() throw();
    bad_exception(const bad_exception&) throw();
    bad_exception& operator=(const bad_exception&) throw();
    virtual ~bad_exception() throw();
    virtual const char* what() const throw();
  };
//}


#endif // __EXCEPTION_H
