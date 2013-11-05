
// good and bad uses of stdlib string functions.

int strncmp(char*, char*, int);
char* strchr(char*, char);
char* strdup(char*);

char good_strncmp(char *str)
{
  if (strncmp(str, "http", 4) == 0)
    return str[4];
}

char bad_strncmp_one(char *str)
{
  if (strncmp(str, "http", 5) == 0)
    return str[5];
}

void call_strncmp(char *str)
{
  good_strncmp(strdup(str));
  bad_strncmp_one(strdup(str));
}

char good_strchr(char *str)
{
  char *pos = strchr(str, 'a');
  if (pos)
    return pos[1];
}

char bad_strchr(char *str)
{
  char *pos = strchr(str, 0);
  if (pos)
    return pos[1];
}
