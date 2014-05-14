int main()
{
  int* buf1;
  int buf2[20];
  int* clean1;
  int clean2[20];
  
  buf1[10] = taint();
  buf2[10] = taint();
  clean1[10] = 2;
  clean2[10] = 2;
  return 0;
}
