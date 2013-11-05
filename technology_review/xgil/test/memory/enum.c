
enum Enum {
  EnumA = 1,
  EnumB,
  EnumC,
  EnumD,
  EnumE
};

int buffer[EnumE];

int foo()
{
  //  for (int i = 0; i < EnumE; i++)
  for (int i = 0; i < 5; i++)
    buffer[i] = 0;
}
