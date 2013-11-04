/*  This file is part of Fuzzgrind.
 *  Copyright (C) 2009 Gabriel Campana
 *
 *  This work is licensed under the terms of the GNU GPL, version 3.
 *  See the LICENSE file in the top-level directory.
 */


/*
 * Monitor a directory for file creation event. A message box is displayed when
 * files are created.
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/inotify.h>

#define EVENT_SIZE    (sizeof(struct inotify_event))
#define BUF_LEN       (1024 * (EVENT_SIZE + 16))
#define DEFAULT_DIR   "../testcase/crash/"

int main(int argc, char **argv) {
    struct inotify_event *event;
    int fd, wd, length, i = 0;
    char buffer[BUF_LEN], *dir;

    fd = inotify_init();
    if (fd < 0) {
        perror("inotify_init");
    }
    
    dir = (argc > 1) ? argv[1] : DEFAULT_DIR;
    wd = inotify_add_watch(fd, dir, IN_CREATE);
    length = read(fd, buffer, BUF_LEN);    

    if (length < 0) {
        perror("read");
    }    

    while (i < length) {
        event = (struct inotify_event *)&buffer[i];
        if (event->len && event->mask & IN_CREATE) {
            if (fork() == 0) {
                execlp("xmessage", "xmessage", "-center", "New crash file !", NULL);
                perror("execlp");
                exit(0);
            }
        }
        i += EVENT_SIZE + event->len;
    }

    inotify_rm_watch(fd, wd);
    close(fd);

    return 0;
}

