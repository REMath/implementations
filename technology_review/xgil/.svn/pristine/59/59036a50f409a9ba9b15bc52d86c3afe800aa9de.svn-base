// exprpath.c
// NUMERRORS 0
// demonstrate a range of expressions with tricky control flow paths
  

void bar(int a, int b);

void foo()
{
  int x,y,z;

  4;
  4.5;
  "foo";
  'f';
  z;
 
  bar(x,y);
  bar(x++,y);
  bar(x,y++);
  //bar(x++,y++);

  bar(x++ + x++, y);
  //bar(x++ + x++, y++);
  
  !(x++);
  
  x && y;
  x++ || y;
  x && y++;
  x++ && y++;
  (x++ + x++) && (y++ + y++);

  x * y;
  x++ + y;
  x * y++;
  x++ * y++;
  (x++ + x++) * (y++ + y++);

  x ? y : z;

  x++ ? y : z;
  x ? y++ : z;
  x ? y : z++;
  
  x++ ? y++ : z;
  x++ ? y : z++;
  x ? y++ : z++;
  
  x++? y++ : z++;
  (x++ + x++)? y++ : z++;
  x++? (y++ + y++) : z++;
  x++? y++ : (z++ + z++);
  
  //x ?: y;
  //x++ ?: y;
  //x ?: y++;
  //x++ ?: y++;
  
  x,y;
  x++, y;
  x, y++;
  x++, y++;

  x = y;
  //(x=y) = z;      // will be illegal once I get lvalue checking..
  //x = (y=z);
  //(x=y) = x++;

  x += y;
  //x++ += y;
  x += y++;
  //x++ += y++;

  x ? y++ :
  y ? z++ :
  z ? x++ : (x=y);

}




