
#include <stdio.h>

#include "file2.h"

#define N 10 		/* nbre maximal de requêtes */

File fileRequete;	/* variable globale */

void init_alea(int x, int y)
{
}

int suivant_alea()
{
    int r = taint();
    return r;
}

int main() {

	unsigned int germe ;	/* pour le generateur aleatoire */
	unsigned int nb_evenements ;
	unsigned int ratio ;
 	unsigned int x ;	/* valeur aleatoire */
	unsigned int i ; 	/* compteur d'evenements */
	unsigned int r, s ; 	/* numeros de requete */ 
	unsigned int p ;	/* numero d'imprimante */

	/* initialisation du generateur aleatoire */
	printf (" germe : ") ;
	scanf ("%d", &germe) ;
	init_alea(germe, 99) ; /* valeurs aleatoires entre 0 et 99 */

	/* lecture des parametres de la simulation */
	printf("\n nombre d'evenements a generer : ") ;
	scanf("%d", &nb_evenements) ;
	printf("\n Pourcentage de \"Requete d'impression\" (entre 0 et 100) : ") ;
	scanf("%d", &ratio) ;
	printf("\n") ;

	/* simulation */
	Initialiser() ;
	r = 0 ;

	for (i=0 ; i<nb_evenements ; i++) {
		x = suivant_alea() ;
		if (x+1>ratio) {
			if (! EstVide()) {
				p = suivant_alea() % P ;
				Extraire (&s, p) ;
				if (s!=-1)
					printf("traitement de la requete %d par l'imprimante %d\n", s, p) ;
			} else
				printf("\t file vide !\n") ;
		} else {
			if (! EstPlein()) {
				p = suivant_alea() % P ;
				printf("insertion de la requete %d pour l'imprimante %d\n", r, p) ;
				Inserer (r, p) ;
				r = r+1 ;
			} else
				printf("\t file pleine !\n") ;
		} ;
	} ;

	return 0 ;

}
