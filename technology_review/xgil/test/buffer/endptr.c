
// inner end pointer example, from snd_usb_find_desc.

int find_desc(void *descstart, int desclen, char type)
{
  char *p, *end, *next;

  p = descstart;
  end = p + desclen;

  for (; p < end;) {

    // equalities:
    // p ~ end - 1
    // p[0] ~ 2
    // p + p[0] ~ end

    // 1 < ubound(p)
    // 1 < ubound(end - p[0])
    // 1 < ubound(end - 2)
    // 1 < ubound(end) + 2
    // 0 <= ubound(end)

    // alternative:
    // 1 < ubound(p)
    // 1 < ubound(end - 1)
    // 1 < ubound(end) + 1
    // 0 < ubound(end)

    if (p[0] < 2) 
      return 0;

    next = p + p[0];
    if (next > end) 
      return 1;

    if (p[1] == type)
      return 2;

    p = next;
  }

  return 4;
}

void call_desc()
{
  char buf[1000];
  find_desc(buf, sizeof(buf), 10);
}

