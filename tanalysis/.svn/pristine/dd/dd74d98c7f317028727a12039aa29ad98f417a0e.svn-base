
#include <stdio.h>
#include <stdlib.h>
#include "arbre.h"


/* --------------------------------------------------- 	*/
/*	Primitives fournies			 	*/
/* --------------------------------------------------- 	*/


Arbre ArbreVide() {
	return NULL ;
}

Arbre Cons (int poid, int car, Arbre fg, Arbre fd) {
	Arbre A ;

	A = (Arbre) malloc(sizeof(struct noeud)) ;
	A->poid = poid ;
	A->car = car;
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

int Poid (Arbre A) {
	return (A->poid) ;
}

int Car (Arbre A) {
	return (A->car) ;
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





