#ifndef __ARBRE__
#define __ARBRE__

/* implementation du type Arbre */

struct noeud {
	        int elem ;
	        struct noeud *fg ;
	        struct noeud *fd ;
        } ;


typedef struct noeud *Arbre ;


/* ----------------------------------------------------------- 	*/
/* constructeurs, destructeur et selecteurs 			*/
/* ----------------------------------------------------------- 	*/

Arbre ArbreVide() ;
  /* renvoie un arbre vide */

Arbre Cons (int elem, Arbre fg, Arbre fd) ;
  /* renvoie un arbre d'element elem, de fils gauche fg et de fils froit fd */

Arbre FilsGauche(Arbre A) ;
  /* renvoie le fils gauche de A */

Arbre FilsDroit(Arbre A) ;
  /* renvoie le fils droit de A */

int Element (Arbre A) ;
  /* renvoie l'element associe a la racine de A */

int EstVide (Arbre A) ;
  /* vaut vrai ssi A est un arbre vide */

int EstFeuille (Arbre A) ;
  /* vaut vrai ssi A est une arbre constitue d'un seul noeud "feuille" */

void Detruire (Arbre A) ;
  /* libere la memoire occupee par l'arbre A (qui devient inutilisable) */

/* ----------------------------------------------------------- 	*/
/* affichage d'un arbre binaire 				*/
/* ----------------------------------------------------------- 	*/

void Afficher(Arbre A) ;
  /* affichage a l'ecran de l'arbre binaire A */

/* ----------------------------------------------------------- 	*/
/* insertion d'un element dans un ABR 				*/
/* ----------------------------------------------------------- 	*/

Arbre Inserer (Arbre A, int x) ;
   /* ajoute l'element x dans l'arbre binaire de recherche A et renvoie */
   /* le nouvel arbre */

/* ----------------------------------------------------------- 	*/
/* recherche d'un element dans un ABR 				*/
/* ----------------------------------------------------------- 	*/

int Recherche (Arbre A, int x) ;
/* renvoie le nombre de comparaisons nécessaires pour accéder 
 * au noeud d'élément x (si ce noeud est présent dans A) 
*/

/* ----------------------------------------------------------- 	*/
/* calcul de grandeurs caracteristiques d'un arbre binaire 	*/
/*	(parametres a completer eventuellement ! ) 		*/
/* ----------------------------------------------------------- 	*/


int NbFeuilles (Arbre A) ;
   /* renvoie le nombre de noeuds "feuille" de l'arbre A */

int Hauteur (Arbre A) ;
   /* renvoie la longeur du plus long chemin racine -> feuille de l'arbre A */

int LgMoyChemin (Arbre A) ;
   /* renvoie la longueur moyenne des chemins  racine -> feuille de l'arbre A */

void NoeudsParNiveau(Arbre A) ;
   /* affiche le nombre de noeuds par niveau de l'arbre A */

int Poids (Arbre A, int n) ;
   /* renvoie le poids de l'arbre A */

#endif
