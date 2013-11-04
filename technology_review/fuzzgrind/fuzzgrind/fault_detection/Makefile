CC=gcc
CFLAGS=-Wall -O4

all: ptrace notify_crash

ptrace: ptrace.c
	$(CC) $(CFLAGS) -o $@ $^
	
notify_crash: notify_crash.c
	$(CC) $(CFLAGS) -o $@ $^

clean:
	rm -f *~ ptrace notify_crash
