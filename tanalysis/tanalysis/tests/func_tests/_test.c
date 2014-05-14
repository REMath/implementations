/* typedef struct {
  int x;
  int y;
} Node;

int *pa, *pb;

int buf[256];
int x;
float y;

void a()
{
	b();
}

void b() 
{
	c();
	d();
	f();
}

void c() 
{
	a();
	d();
}

void d() 
{
	e();
}

void e() 
{
	d();
}

void f() 
{
	e();
	g();
}

void g() 
{
	f();
	h();
}

void h() 
{
	g();
}

int test(int n)
{
	if (n > 0)
		test(n-1);
}
*/

typedef struct {
	int a;
	int b;
} s_type;

int main (int argc, char** argv)
{
	int a;
	a = (int)((float*)argv[1]);
	return 0;
}   
