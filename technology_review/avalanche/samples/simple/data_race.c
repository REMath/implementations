#include <pthread.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>

int race_target;
int race_target2;
char x[4];

void* child_func(void* data)
{
    if (((x[0] == 'b') &&
        (x[1] == 'a') &&
        (x[2] == 'd') &&
        (x[3] == '!')) ||
            ((x[0] == 'e') &&
             (x[1] == 'e')))
    {
        race_target ++;
    }
    if ((x[0] == 'e') &&
        (x[1] == 'e'))
    {
        race_target2 ++;
    }
    return NULL;
}

int main(int argc, char **argv)
{
    int fd = open(argv[1], O_RDONLY, S_IRWXU);
    read(fd, x, 4);
    pthread_t tid;
    pthread_create(&tid, NULL, child_func, NULL);
    race_target ++;
    if ((x[2] == 'w') &&
        (x[3] == 'q'))
    {
        race_target2 ++;
    }
    pthread_join(tid, NULL);
    return 0;
}
