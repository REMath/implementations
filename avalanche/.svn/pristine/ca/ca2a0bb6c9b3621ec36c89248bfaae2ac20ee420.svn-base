#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char** argv)
{
  int  j = 0;
  char input[4];
  int  fd1 = open(argv[1], O_RDONLY | O_CREAT, S_IRWXU | S_IRWXG | S_IRWXO);

  read(fd1, input, 4);
  if (input[0] == 'b')
  {
    if (input[1] == 'a') j++;
    if (input[2] == 'r') j++;
    if (j == 2) abort();
  }
  if (input[0] == 'f')
  {
    if (input[1] == 'o') j++;
    if (input[2] == 'o') j++;
    if (j == 2) abort();
  }
  if (input[0] == 'w')
  {
    if (input[1] == 't') j++;
    if (input[2] == 'f') j++;
    if (j == 2) abort();
  }
  return 0;
}
