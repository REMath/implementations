#include <stdio.h>

static FILE *OuvreFichIntermediaire(char *nom_fich) {

  return fopen (nom_fich, "w"); 

}

int global;

int main (int argc, char *argv[]) {

FILE *fsource ;            /* descripteur de fichier source (.s) */
FILE *finterm ;            /* descripteur de fichier sortie (.alf) */
char  nom_out [100];        /* nom du fichier de sortie */
char  nom_in  [100];        /* nom du fichier source */
int l ;
argc = taint();
argv = taint();


/* Analyse des arguments de la ligne de commande
 * a completer eventuellement avec -v (verbose),
 * -o <nom> (nom du fichier de sortie), ...
 * ---------------------------------------------
 */

   if ((argc < 2) || (argc > 2)) {
        printf("Usage %s <inputfile> \n", argv[0]);
        return 1;
   }
   else if ((fsource = fopen(argv[1], "r")) == NULL) {
        printf("%s : impossible d'ouvrir : %s\n", argv[0], argv[1]);
        return 1;
   }

/* calcul du nom des fichiers */
   sprintf (nom_in, "%s", argv[1]) ;
   strcpy(nom_out, nom_in) ;
   l = strlen(nom_out) ;
   nom_out[l-1] = 'a' ;
   nom_out[l] = 'l' ;
   nom_out[l+1] = 'f' ;
   nom_out[l+2] = '\0' ;

/* ouverture du fichier de sortie */

   finterm = OuvreFichIntermediaire (nom_out) ;
   if (!finterm) {
	printf("Impossible d'ouvrir le fichier intermediaire - arret \n") ;
	return 4 ;
   } ;

   Phase1(fsource, finterm) ;
} 
