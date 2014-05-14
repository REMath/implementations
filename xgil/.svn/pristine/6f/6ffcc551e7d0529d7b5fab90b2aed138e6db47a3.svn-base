// test loop identification, back edge breaking

# 1 "nested.c"
void nested(char *a)
{
  while (*a) {
    while (*a) {
      a++;
    }
    a++;
  }
}

# 1 "massive_case.c"
int massive_case(int x)
{
  switch (x) {
  case 1:
    return 1;
  case 2:
    return 2;
  case 10 ... 10000:
    return 3;
  default:
    return 4;
  }
}

# 1 "noloop.c"
void noloop(char *a)
{
  do {
    a++;
  } while (0);
}

# 1 "basic.c"
void basic(char *a)
{
  a++;
  while (*a) {
    a++;
  }
}

# 1 "gotos.c"
void gotos(char *a)
{
 L:
  a++;
  if (*a)
    goto L;
}

# 1 "irreducible.c"
void irreducible(char *a, int b)
{
  if (b) {
    goto L;
  }

  while (*a) {
    a++;
    L:
    a++;
  }
}

# 1 "more_irreducible.c"
void more_irreducible(char *a, int b, int c)
{
  if (b==0) { goto L0; }
  if (b==1) { goto L1; }

  while (*a) {
    if (c) {
    L0: a++;
    }
    else {
    L1: a--;
    }
    a++;
  }
}

# 1 "irreducible_nest1.c"
void irreducible_nest1(char *a, int b, char *z)
{
  while (*z) {
    if (b) {
      goto L0;
    }

    while (*a) {
      a++;
      L0:
      a++;
    }

    if (b) {
      goto L1;
    }

    while (*a) {
      a++;
      L1:
      a++;
    }
  }
}

# 1 "irreducible_nest2.c"
void irreducible_nest2(char *a, int b, char *z)
{
  if (b) {
    goto L0;
  }

  while (*a) {
    a++;
  L0:
    while (*z) { *z++; }
  }
}

# 1 "irreducible_nest2.c"
void irreducible_nest3(char *a, int b, char *z)
{
  if (b) {
    goto L0;
  }

  while (*a) {
    a++;
  L0:
    a++;
    while (*z) { *z++; }
  }
}

# 1 "deeper_nested.c"
void deeper_nested(char *a)
{
  while (*a) {
    while (*a) {
      while (*a) {
      }
    }
    while (*a) {
    }
  }
}

# 1 "complex.c"
void complex(char *a)
{
  a++;
  while (*a) {
    if (*a) goto L;
  }
  a++;
 L:
  a++;
}

# 1 "loopforever.c"
void loopforever(char *a)
{
  while (1) {}
}

# 1 "buffer_append_space.c"

typedef struct Buffer {
 unsigned char *buf;
 unsigned int alloc;
 unsigned int offset;
 unsigned int end;
} Buffer;

// openssh/buffer.c
void *buffer_append_space(Buffer *buffer, unsigned int len)
{
	unsigned int newlen;
	void *p;

	if (len > 0x100000)
		fatal("buffer_append_space: len %u not supported", len);

	if (buffer->offset == buffer->end) {
		buffer->offset = 0;
		buffer->end = 0;
	}
restart:
	if (buffer->end + len < buffer->alloc) {
		p = buffer->buf + buffer->end;
		buffer->end += len;
		return p;
	}
	if (buffer->offset > buffer->alloc / 2) {
		memmove(buffer->buf, buffer->buf + buffer->offset,
			buffer->end - buffer->offset);
		buffer->end -= buffer->offset;
		buffer->offset = 0;
		goto restart;
	}
	newlen = buffer->alloc + len + 32768;
	if (newlen > 0xa00000)
		fatal("buffer_append_space: alloc %u not supported",
		    newlen);
	buffer->buf = xrealloc(buffer->buf, newlen);
	buffer->alloc = newlen;
	goto restart;
}
