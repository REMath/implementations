
typedef struct fubar
{
  int x;
  int y;
} fubar;

fubar g_list[] =
{
  { 1, 2 },
  { 3, 4 },
  { 5, 6 },
  { -1, -1 }
};

void use_list(fubar *list)
{
  int ty = 0;
  while (list->x != -1) {
    ty += list->y;
    list++;
  }
}

void call_list()
{
  use_list(&g_list);
}
