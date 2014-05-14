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
 
int main(int argc, char** argv)
{
  struct sockaddr_in stSockAddr;
  int res;
 
  memset(&stSockAddr, 0, sizeof(struct sockaddr_in));
 
  stSockAddr.sin_family = AF_INET;
  stSockAddr.sin_port = htons(atoi(argv[1]));
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

  int sd = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);

  if (sd == -1)
  {
    perror("cannot create socket");
    exit(EXIT_FAILURE);
  }
    
  res = connect(sd, (const struct sockaddr*)&stSockAddr, sizeof(struct sockaddr_in));
 
  if(res < 0)
  {
    perror("error connect failed");
    close(sd);
    exit(EXIT_FAILURE);
  }

  char a;
  read(sd, &a, 1);
  int b;
  b = 3 / (5 - a);

  shutdown(sd, SHUT_RDWR);
  close(sd);

  return 0;
}

