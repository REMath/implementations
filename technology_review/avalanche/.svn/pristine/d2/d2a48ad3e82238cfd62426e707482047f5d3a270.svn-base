/* Client code in C */
 
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

char global[5];
 
int main(void)
{
  struct sockaddr_in stSockAddr;
  int res;
 
  memset(&stSockAddr, 0, sizeof(struct sockaddr_in));
 
  stSockAddr.sin_family = AF_INET;
  stSockAddr.sin_port = htons(10000);
  res = inet_pton(AF_INET, "127.0.0.1", &stSockAddr.sin_addr);
 
  if (res < 0)
  {
    perror("error: first parameter is not a valid address family");
    exit(EXIT_FAILURE);
  }
  else if (res == 0)
  {
    perror("char string (second parameter does not contain valid ipaddress");
    exit(EXIT_FAILURE);
  }

  int cfds[4];

  int i = 0;
  for (; i < 4; i++)
  {
    cfds[i] = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);

    if (cfds[i] == -1)
    {
      perror("cannot create socket");
      exit(EXIT_FAILURE);
    }
    
    res = connect(cfds[i], (const struct sockaddr*)&stSockAddr, sizeof(struct sockaddr_in));
 
    if(res < 0)
    {
      perror("error connect failed");
      close(cfds[i]);
      exit(EXIT_FAILURE);
    }
  }    

  int  j = 0;
  char input1, input2, input3, input4;
  read(cfds[0], &input1, 1);
  read(cfds[1], &input2, 1);
  read(cfds[2], &input3, 1);
  read(cfds[3], &input4, 1);
  if (input1 == 'b') j++;
  if (input2 == 'a') j++;
  if (input3 == 'd') j++;
  if (input4 == '!') j++;
  if (j == 4) abort();
 
  for (i = 0; i < 4; i++)
  {
    shutdown(cfds[i], SHUT_RDWR);
    close(cfds[i]);
  }

  return 0;
}

