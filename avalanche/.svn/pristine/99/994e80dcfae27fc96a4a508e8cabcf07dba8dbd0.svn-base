#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>

char global[5];

int main()
{
  int i;
  char local[3];
  int fd1 = open("qq.txt", O_RDONLY | O_CREAT);
  read(fd1, local, 3);
  if (local[1] < 5) {
    i = 0;
  }
  global[i] = 0;
  return 0;
}

