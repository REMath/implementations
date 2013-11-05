#include <stdio.h>

#include "permutation_aleatoire.h"
#include "arbre.h"

#define NB_ELEM_MAX 5000	/* taille maximale de la permutation */

int main()
{
  int T[NB_ELEM_MAX];		/* pour memoriser la permutation */
  int n ;			/* nbre d'elements de la permutation */
  int i,j ;
  int nb_essais ;		/* nombre d'essais */
  unsigned int germe ;		/* germe pour le generateur aleatoire */
  Arbre A ;			/* l'arbre binaire de recherche */
  int cout_acces ; 		/* cout de l'acces a l'ensemble des noeuds de A */


  /* lecture des parametres du test */
  printf("germe ? ") ;
  scanf("%d", &germe) ;
  printf("nb essais ? ") ;
  scanf("%d", &nb_essais) ;
  do {
  	printf("taille du tableau (comprise entre 0 et %d) ? ", NB_ELEM_MAX);
  	scanf ("%d", &n) ;
     }
  while ((n>NB_ELEM_MAX) || (n<0)) ;

  init_alea (germe, (unsigned int) 2*n) ;

  for (i = 0 ; i < nb_essais ; i++) {

	/* generation d'une permutation aleatoire dans T[0..n] */
  	permutation_aleatoire (T, n) ;
	printf(" Permutation : ") ;
	affiche_permutation (T, n) ; 

	/* construction d'un arbre binaire de recherche a partir de T[0..n-1] */
	A = ArbreVide() ;
	for (j=0 ; j<n ; j++) {
		A = Inserer(A, T[j]) ;
	} ;

	/* cout de l'acces à chacun de ses éléments (question 8) */

	cout_acces = 0 ;
	for (j=0 ; j<n ; j++) 
		cout_acces = cout_acces + Recherche(A, j) ;
	

	/* affichage des caracteristiques de l'arbre */
	printf(" \n ABR obtenu : \n ") ;
	Afficher (A) ;  
	printf ("\n  Caracteristiques de l'ABR :\n") ;
	printf ("      - nbre de feuilles : %d\n", NbFeuilles(A));
	printf ("      - hauteur maximale : %d\n", Hauteur(A));
	printf ("      - longueur moyenne des chemins : %d\n", LgMoyChemin(A));
	printf ("      - nombre de noeuds par niveau :\n") ; NoeudsParNiveau(A);
	printf ("      - poids : %d\n", Poids(A,n));
	printf ("      - cout de l'acces : %d\n", cout_acces);
	printf ("--------------------------------------------------------\n") ;

	/* destruction de l'arbre */
	Detruire (A) ;

  } ; 

  return 0;
}
