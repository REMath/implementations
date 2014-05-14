
// simplified from vr_ParseVersion

void parse_version(char *verstr)
{
  while (*verstr && *verstr != '.')
    verstr++;
  if (*verstr) {
    verstr++;
    while (*verstr && *verstr != '.')
      verstr++;
  }
}

void call_parse()
{
  parse_version("fubar");
}
