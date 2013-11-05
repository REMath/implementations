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

  /* Answer must contain NEEDLE2; we don't need to skip it. */ 
  if (istrstr(answer, NEEDLE2) == -1)
    return 0;

  /* Find (something)\r(something)\r, where each (something) is at
   * least MIN_DIFF characters
   *
   * If we don't find anything satisfying that, abort
   */
  for( end=beginning ; answer[end] != EOS && answer[end] != '\r' ; end++ );
  if ( answer[end] == EOS || end-beginning < MIN_DIFF)
    return 0;
  for( end=end+1 ; answer[end] != EOS && answer[end] !='\r' ; end++ );
  if ( answer[end] == EOS || end-beginning < MIN_DIFF )
    return 0;

  /* Change the last '\r' to an EOS */
  answer[end] = EOS;

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
