#include <stdio.h>
#include <stdlib.h>

typedef struct {
    int r_w;
    FILE* file;
    int nb_bit;
    int which_bit;
    int octet;
} BFILE;

/*
BFILE *bstart(FILE *fichier, const char *mode)
{
  int a;
  int* p = (int* ) malloc (a); 
  BFILE *bf = (BFILE*) malloc (sizeof(BFILE));
  return bf;
}
*/

BFILE *bstart(FILE *fichier, const char *mode)
{
  
  BFILE *bf = (BFILE*) malloc (sizeof(BFILE));
  if (bf == NULL) return 0;
  if (*mode == 'r')
    bf->r_w = 0;  //mode lecture
  else if (*mode == 'w')
    bf->r_w = 1;  //mode ecriture
  bf->file = fichier;
  bf->nb_bit =0;
  bf->which_bit = 7;//va de 7 a 0
  bf->octet = 0;
  return bf;
}