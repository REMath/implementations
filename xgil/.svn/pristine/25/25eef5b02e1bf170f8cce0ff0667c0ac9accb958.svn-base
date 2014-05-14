
void callee1() {}
void callee2() {}
void callee3() {}

void scc1();
void scc2();
void scc3();

void (*pfn)();
void indirect1() { pfn(); }
void indirect2() { pfn(); }

void scc1()
{
  scc2();
  callee1(); indirect1();
}

void scc2()
{
  scc3();
  callee2(); indirect2();
}

void scc3()
{
  scc1();
  callee3();
}

void caller1() { scc1(); }
void caller2() { scc2(); }
void caller3() { scc3(); }

void par_caller1() { caller1(); }
void par_caller2() { caller2(); }
void par_caller3() { caller3(); }
