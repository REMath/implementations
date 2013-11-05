
#include <stdio.h>
#include <stdlib.h>
#include "arbre.h"


/* --------------------------------------------------- 	*/
/*	constructeurs, destructeur et selecteurs 	*/
/* --------------------------------------------------- 	*/


Arbre ArbreVide() {
	return NULL ;
}

Arbre Cons (int elem, Arbre fg, Arbre fd) {
	Arbre A ;

	A = (Arbre) malloc(sizeof(struct noeud)) ;
	A->elem = elem ;
	A->fg = fg ;
	A->fd = fd ;
	return A ;
}

Arbre FilsGauche(Arbre A) {
	return (A->fg) ;
}

Arbre FilsDroit(Arbre A) {
	return (A->fd) ;
}

int Element (Arbre A) {
	return (A->elem) ;
}

int EstVide (Arbre A) {
	return (A == NULL) ;
}

int EstFeuille(Arbre A) {
	return (A != NULL && EstVide(FilsGauche(A)) && EstVide(FilsDroit(A))) ;
}


void Detruire (Arbre A) {
	if (!EstVide(A)) {
		Detruire (FilsGauche(A)) ;
		Detruire (FilsDroit(A)) ;
		free (A) ;
	} 
}


/* --------------------------------------------------- 	*/
/*	Affichage d'un arbre binaire			*/
/* --------------------------------------------------- 	*/

static void Parcours_Affiche (Arbre A, int niveau) {
	int i ;

	if (!EstVide(A)) {
		for (i=0 ; i<niveau ; i++)
			printf("    ") ;
		printf ("%d\n", Element(A)) ;
		Parcours_Affiche (FilsDroit(A), niveau+1) ;
		Parcours_Affiche (FilsGauche(A), niveau+1) ;
	}
}

static void Parcours_Affiche_2 (Arbre A, FILE *f) {

	if (!EstVide(A)) {

		if (!EstVide(FilsGauche(A)))
			fprintf(f, "\t %d -> %d ;\n", Element(A), Element(FilsGauche(A))) ; 
		if (!EstVide(FilsDroit(A)))
			fprintf(f, "\t %d -> %d ;\n", Element(A), Element(FilsDroit(A))) ; 
		Parcours_Affiche_2 (FilsDroit(A), f) ;
		Parcours_Affiche_2 (FilsGauche(A), f) ;
	}
}


void Afficher (Arbre A) {
	FILE *f = fopen("resultat.dot", "w") ;
	Parcours_Affiche (A, 0) ;
	fprintf(f, "digraph Arbre {\n") ;
	Parcours_Affiche_2 (A, f) ;
	fprintf(f, "}\n") ;
	fclose (f) ;
}


/* --------------------------------------------------- 	*/
/*	Insertion d'un element dans un ABR		*/
/* --------------------------------------------------- 	*/


Arbre Inserer (Arbre A, int x) {
	
	if (EstVide(A)) {
		return Cons(x, ArbreVide(), ArbreVide()) ;
	} else {
		if (Element(A) > x) 
		  return Cons (Element(A), Inserer(FilsGauche(A), x), FilsDroit(A)) ;
		else
		  return Cons (Element(A), FilsGauche(A), Inserer(FilsDroit(A), x)) ;
	}
}

/* --------------------------------------------------- 	*/
/*	Recherche d'un élément dans un ABR		*/
/* --------------------------------------------------- 	*/

int Recherche (Arbre A, int x) {
/* renvoie le nbre de comparaisons necessaires pour trouver x */

	if (EstVide(A))
		return 0 ;
	else {
		if (Element(A) == x)  
			return 1 ;
		else {
			if (Element(A) > x) 
				return 2 + Recherche (FilsGauche(A), x) ;
			else
				return 2 + Recherche (FilsDroit(A), x) ;

		}
	}
}


/* ------------------------------------------------------------ */
/* 	calcul de grandeurs caracteristiques d'un arbre binaire */
/* ------------------------------------------------------------ */


	/* A COMPLETER EN UTILISANT LES CONSTRUCTEURS ET SELECTEURS */



int NbFeuilles (Arbre A) {

	if (!EstVide(A)) {
		if (EstFeuille(A)) 
			return 1 ;	/* une feuille */
		else
			/* somme des feuilles des sous-arbres gauche et droit */
			return (NbFeuilles(FilsGauche(A)) + 
					NbFeuilles(FilsDroit(A))) ;
	} else {
		return 0 ; /* un arbre vide n'a pas de feuille */
	}
}


static int max (int h1, int h2) {
	if (h1>h2) 
		return h1 ;
	else
		return h2 ;
}

int Hauteur (Arbre A) { 
	if (!EstVide(A)) {
		if (EstFeuille(A)) 
		      return 1 ;	/* une feuille, arbre de hauteur 1 */
		else
		      /* 1 + max des hauteurs des sous-arbres gauche et droit */
		      return 1 + 
			max(Hauteur(FilsGauche(A)), Hauteur(FilsDroit(A)));
	} else {
		return 0 ; /* un arbre vide est de hauteur 0 */
	}
		
} ;


static int somme_longueurs_chemins (Arbre A) {
/* calcule la somme des longueurs de l'ensemble des chemins de A */

	int res = 0 ; /* resultat */

	if (EstFeuille(A)) 
		res=0 ;  /* feuille, une seul chemin de longueur 0 */
	else {
		/* si le fils gauche existe on ajoute 1 a la somme des 
		   longueurs de ses chemins */
		if (!EstVide(FilsGauche(A))) 
		   res = res + NbFeuilles(FilsGauche(A)) + 
			   	somme_longueurs_chemins(FilsGauche(A));

		/* idem pour le fils droit */
		if (!EstVide(FilsDroit(A))) 
		   res = res + NbFeuilles(FilsDroit(A)) + 
			   	somme_longueurs_chemins(FilsDroit(A));
       } ;

       return res ;
}

int LgMoyChemin (Arbre A) {

	int nbc = NbFeuilles (A) ; /* il y a autant de chemins que de feuilles */
	
	/* calcul de la somme des longueurs de tous les chemins de A */
	int l = somme_longueurs_chemins (A) ;

	/* on divise par le nombre de chemins pour obtenir la longeur moyenne */
	return (l / nbc) ; 
}


static void parcours_niveaux (Arbre A, int niveau, int t[]) {
/* calcule dans t[i] le nombre de noeuds de niveau i de l'arbre A */
	if (!EstVide(A)) {
		parcours_niveaux (FilsGauche(A), niveau+1, t) ;
		parcours_niveaux (FilsDroit(A), niveau+1, t) ;
		t[niveau] = t[niveau] + 1 ;
	} ;  
	
} 


void NoeudsParNiveau(Arbre A) {

	int h = Hauteur(A) ;
	int noeuds_par_niveaux[h] ;
	int i ;

	for (i=0 ; i<h ; i++)
		noeuds_par_niveaux[i] = 0 ;

	parcours_niveaux (A, 0, noeuds_par_niveaux) ;

	for (i=0 ; i<h ; i++)
		printf(" \t nombre de noeuds de niveau %d : %d \n",
				i, noeuds_par_niveaux[i]) ;
}


int Poids (Arbre A, int n) {

	int h = Hauteur(A) ;
	int noeuds_par_niveaux[h] ;

	int i, poids=0 ;
	for (i=0 ; i<h ; i++)
		noeuds_par_niveaux[i] = 0 ;

	parcours_niveaux (A, 0, noeuds_par_niveaux) ;
	for (i=0; i<h ; i++)
		poids = poids+i*noeuds_par_niveaux[i] ;
	return poids ;
}

