#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>

int i = 0;
int exploit_i = 0;
int* d;

void f1(char value)
{
  if (value < 1)
  {
    i++;
  }
}

void f2(char value)
{
  if (value < 2)
  {
    i++;
  }
}

void f3(char value)
{
  if (value < 5)
  {
    i++;
  }
}

void f4(char value)
{
  if (value < 13)
  {
    exploit_i++;
  }
}

int main(int argc, char** argv)
{
  int j, fd1 = open(argv[1], O_RDONLY | O_CREAT, S_IRWXU | S_IRWXG | S_IRWXO);
  char input[4];
  read(fd1, input, 4);
  f1(input[0]);
  f2(input[1]);
  f3(input[2]);
  f4(input[3]);
  if (exploit_i)
  {
    d = (int*) malloc(sizeof(int));
  }
  *d = 1;
  return 0;
}

