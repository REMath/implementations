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
  if (input[0] == 'm') j++;
  if (input[1] == 'o') j++;
  if (input[2] == 'o') j++;
  if (input[3] == '!') j++;
  if (j == 4) 
  {
    int m;
    printf("m=%d\n", m);
  }
  return 0;
}
