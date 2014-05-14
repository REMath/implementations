#ifndef __ARBRE__
#define __ARBRE__

/* implementation du type Arbre */

struct noeud {
	        int car ;
	        int poid ;
	        struct noeud *fg ;
	        struct noeud *fd ;
        } ;


typedef struct noeud *Arbre ;


/* ----------------------------------------------------------- 	*/
/* constructeurs, destructeur et selecteurs 			*/
/* ----------------------------------------------------------- 	*/

Arbre ArbreVide() ;
  /* renvoie un arbre vide */

Arbre Cons (int poid, int car, Arbre fg, Arbre fd) ;
  /* renvoie un arbre d'element elem, de fils gauche fg et de fils froit fd */

Arbre FilsGauche(Arbre A) ;
  /* renvoie le fils gauche de A */

Arbre FilsDroit(Arbre A) ;
  /* renvoie le fils droit de A */

int Poid (Arbre A) ;
  /* renvoie le poids associe a la racine de A */

int Car (Arbre A);
	/* renvoie le caractere associe a la racine de A */

int EstVide (Arbre A) ;
  /* vaut vrai ssi A est un arbre vide */

int EstFeuille (Arbre A) ;
  /* vaut vrai ssi A est une arbre constitue d'un seul noeud "feuille" */

void Detruire (Arbre A) ;
  /* libere la memoire occupee par l'arbre A (qui devient inutilisable) */





#endif
