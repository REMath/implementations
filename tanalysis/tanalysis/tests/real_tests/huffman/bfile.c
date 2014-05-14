#include <stdio.h>
#include <stdlib.h>
#include "bfile.h"


/*
   bstart
   description : ouvre un acces bit a bit en lecture (mode "r") ou bien en
                 ecriture (mode "w") au fichier dont le descripteur est passe
                 en parametre (le fichier doit avoir ete prealablement ouvert).
                 Pour conserver la coherence des donnees, aucun acces non bit a
                 bit ne doit etre fait jusqu'au prochain bstop
   parametres : descripteur du fichier, mode d'ouverture de l'acces
   valeur de retour : pointeur vers une structure BFILE allouee par bstart
                      ou NULL si une erreur est survenue
   effets de bord : lit potentiellement en avance dans le fichier
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

/*
   bstop
   description : ferme un acces bit a bit a un fichier prealablement ouvert par
                 bstart (termine les E/S en attente et libere la structure
                 BFILE).
   parametres : pointeur vers une structure BFILE renvoyee par bstart
   valeur de retour : 0 si aucune erreur n'est survenue
   effets de bord : ecrit potentiellement dans le fichier
*/
int bstop(BFILE *fichier)
{
  if (fichier->r_w == 1)
  {
    while((fichier->which_bit) >=0 ){
      bitwrite(fichier, 0);  
    }
    fputs(&((*fichier).octet), (*fichier).file);
  }

  free(fichier);
  return 0;
  
}
/*
   bitread
   description : lit un bit dans un fichier sur lequel un acces bit a bit en
                 lecture a ete prealablement ouvert a l'aide de bstart.
   parametres : pointeur vers une structure BFILE renvoyee par bstart
   valeur de retour : bit lu ou -1 si une erreur s'est produite
   effets de bord : valeur de retour depend du contenu du fichier
                    lit potentiellement en avance dans le fichier
*/
int bitread(BFILE *fichier){
  if ((fichier->which_bit==7)  || (fichier->which_bit < 0))
    {
      fichier->octet = fgetc(fichier->file);
      fichier->which_bit = 7;
      }

  if (fichier->octet == EOF) return -1;

  if ((fichier->which_bit <= 7) && (fichier->which_bit >= 0))
    {
      fichier->which_bit--;
      return (fichier->octet >> (fichier->which_bit+1)) & 1;
    }
 
  return -1;
  }

/*
   bitwrite
   description : ecrit un bit dans un fichier sur lequel un acces bit a bit en 
                 ecriture a ete prealablement ouvert a l'aide de bstart.
   parametres : pointeur vers une structure BFILE renvoyee par bstart, bit a
                ecrire
   valeur de retour : -1 si une erreur s'est produite
   effets de bord : ecrit potentiellement dans le fichier
*/
int bitwrite(BFILE *fichier, int bit) {
  if((*fichier).which_bit < 0){
    fputs(&(fichier->octet), fichier->file);
    fichier->octet = 0;
    fichier->which_bit = 7;
  }

  if(bit == 1){
    char tmp = 0;
    tmp =  1 << fichier->which_bit;
    fichier->octet = fichier->octet | tmp;
    fichier->which_bit--;
  }
  else if (bit == 0)
    fichier->which_bit--;
 
  return 0;
}

/*
   beof
   description : retourne 1 si il ne reste plus aucun bit a lire dans le
                 fichier sur lequel un acces bit a bit en lecture a ete
                 prealablement ouvert a l'aide de bstart, 0 sinon.
   parametres : pointeur vers une structure BFILE renvoyee par bstart
   valeur de retour : 1 ou 0
   effets de bord : lit potentiellement dans le fichier
*/
int beof(BFILE *fichier){
  if (feof(fichier->file)) 
      {printf("zut\n");return 1;}
  else if (fichier->octet == EOF)
    return 1;
  else 
    return 0;
}


