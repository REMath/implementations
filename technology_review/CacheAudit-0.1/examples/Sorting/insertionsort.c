// Source from http://www.codebeach.com/2008/09/sorting-algorithms-in-c.html
//# include <stdio.h>

int main(){

  unsigned int a[64];
  unsigned int array_size=64;  
  unsigned int i, j, index;

  for (i = 1; i < array_size; ++i)
    {
      index = a[i];
      for (j = i; j > 0 && a[j-1] > index; j--)
	a[j] = a[j-1];
      
      a[j] = index;
    }

  // for (i =0;i<array_size;i++)
  // printf ("%d\n", a[i]);

}

