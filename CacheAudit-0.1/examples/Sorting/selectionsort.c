// Source from http://www.codebeach.com/2008/09/sorting-algorithms-in-c.html
//# include <stdio.h>

int main(){

  unsigned int a[64];
  unsigned int array_size=64;  

  int i;
  for (i = 0; i < array_size - 1; ++i)
    {
      int j, min, temp;
      min = i;
      for (j = i+1; j < array_size; ++j)
	{
	  if (a[j] < a[min])
	    min = j;
	}

      temp = a[i];
      a[i] = a[min];
      a[min] = temp;
    }

  //   for (i =0;i<array_size;i++)
  //   printf ("%d\n", a[i]);

}
