#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>

void* malloc(size_t sz)
{
    char *ptr = "malloc\n";
    printf("%s",ptr);
    void *(*libc_malloc)(size_t) = dlsym(RTLD_NEXT, "malloc");
    return libc_malloc(sz);
}

void free(void *p)
{
    char *ptr = "free\n";
    printf("%s",ptr);
    void (*libc_free)(void*) = dlsym(RTLD_NEXT, "free");
    libc_free(p);
}


int main()
{
    free(malloc(10));
    return 0;
}
