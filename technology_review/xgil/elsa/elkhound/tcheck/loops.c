// loops.c
// NUMERRORS 0
// test my CFG extraction

void foo()
{ 
  int x,y,z;

  ;       // skip

label1:
  x=4;
  
  switch (y) {
    case 1: y=6; break;
    case 2: y=7;
    case 3: z=9; break;
    case 4 ... 5: z=3; break;
    default: x=5;
  }
  
  switch (y) {
    default: y=9; break;
  }
  
  {
    x=1;
    y=2;
    z=3;
  }
  
  if (x > y) {
    z=9;
  }
  else {
    z=10;
  }
  
  x=5;
  
  while (z<10) {
    z++;
  }

  x=6;

  do {
    x++;
  } while (x < 8);

  for (y=0; y<5; y++) {
    z--;
  }

  while (z<10) {
    z++;
    if (y++) {
      break;
    }
    if (x<9) {
      continue;
    }
    x += 5;
  }
  
  if (z > y) {
    return;
  }        
  
  if (x > y) {
    goto label1;
  }
  else {
    goto label2;
  }
  
  x=9;
  
label2:
  x=8;
}




