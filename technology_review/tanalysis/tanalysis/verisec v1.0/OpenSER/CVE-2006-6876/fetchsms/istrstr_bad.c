#include "../constants.h"

int fetchsms (char *pdu, int sim)
{
  char answer[ANSWERSIZE];
  int position;
  int beginning;
  int end;
  int  foo,err;

  /* Added for STAC: the input data must be considered tainted! */
  answer[0] = taint();
  
  /* Input magically appears */
  answer[ANSWERSIZE-1] = EOS;

  /* Search for NEEDLE and skip it */
  position=istrstr(answer,NEEDLE);
  if (position==-1)
    return 0;
  beginning = position + NEEDLE_SZ + 1;

  /* BAD */
  r_strcpy(pdu,answer+beginning);
  
  return sim;
}

int main ()
{
  char pdu [PDUSIZE];
  int sim = 0;

  fetchsms (pdu, sim);

  return 0;
}
