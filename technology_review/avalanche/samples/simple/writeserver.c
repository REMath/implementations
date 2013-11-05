/* Server code in C */
 
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
  int sfd = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);

  if(sfd == -1)
  {
    perror("can not create socket");
    exit(EXIT_FAILURE);
  }
 
  memset(&stSockAddr, 0, sizeof(struct sockaddr_in));
 
  stSockAddr.sin_family = AF_INET;
  stSockAddr.sin_port = htons(10000);
  stSockAddr.sin_addr.s_addr = INADDR_ANY;

  int bindRes = bind(sfd, (const struct sockaddr*)&stSockAddr, sizeof(struct sockaddr_in));
 
  if(bindRes == -1)
  {
    perror("error bind failed");
    close(sfd);
    exit(EXIT_FAILURE);
  }

  int listenRes = listen(sfd, 10);
 
  if(listenRes == -1)
  {
    perror("error listen failed");
    close(sfd);
    exit(EXIT_FAILURE);
  }
 
  for(;;)
  {
    char c[4] = {1, 1, 1, 1};
    int cfd = accept(sfd, NULL, NULL);
 
    if(cfd < 0)
    {
      perror("error accept failed");
      close(sfd);
      exit(EXIT_FAILURE);
    }
 
    write(cfd, c, 4);
 
    shutdown(cfd, SHUT_RDWR);
    close(cfd);
  }
  return 0;
}

