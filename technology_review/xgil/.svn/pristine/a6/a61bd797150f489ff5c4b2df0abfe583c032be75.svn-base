
struct str1
{
  union { int a; int b; };
};

struct str2
{
  str1 f;
};

void foo(str2 *sa, str2 *sb)
{
  sa->f = sb->f;
}
