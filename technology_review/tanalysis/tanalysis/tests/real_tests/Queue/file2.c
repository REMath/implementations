#include <stdlib.h>
#include <stdio.h>
#include "file2.h"


extern File fileRequete ;   /* declaration de la variable globale externe FileRequetes */ 



/* implementation des operateurs de la File d'Attente */
/* (FICHIER A COMPLETER ...) */


/* --------------------------------------------------
 * Initialiser
 * parametres : aucun
 * resultat : aucun
 * description : initialise la variable globale FileRequetes
 * effet de bord : FileRequetes est modifiée
 ----------------------------------------------------- */

void Initialiser () {
	fileRequete = NULL;
}

/* --------------------------------------------------
 * EstVide
 * parametres : aucun
 * resultat : un booleen
 * description : vaut vrai ssi la variable globale FileRequetes est vide
 * effet de bord : aucun
 ----------------------------------------------------- */

int  EstVide () {
		
	return fileRequete==NULL;
}

/* --------------------------------------------------
 * EstPlein
 * parametres : aucun
 * resultat : un booleen
 * description : vaut vrai ssi la variable globale FileRequetes est pleine
 * effet de bord : aucun
 ----------------------------------------------------- */

int nbRequetesImp(int imp)
{
	int cpt =0;
	File tete = fileRequete;
	while (tete!=NULL)
	{
			if (tete->imprimante==imp)cpt++;
			tete = tete->suivant;
	}
	return cpt;
}

int nbRequetesTotal()
{
		int nbt=0;
		int i;
		for (i=0; i<P; i++)
		{
				nbt+=nbRequetesImp(i);
		}
		return nbt;
}


int  EstPlein () {

	return (nbRequetesTotal()>MAXREQUETES);
}

/* --------------------------------------------------
 * Inserer
 * parametres : un entier x (donné),  un entier p (donné)
 * resultat : aucun
 * description :  insere la nouvelle requête x destinée à l'imprimente p
 * 			dans la variable globale FileRequetes
 * effet de bord : FileRequetes est modifiée
 ----------------------------------------------------- */

void Inserer (unsigned int x, unsigned int p) 
{
		File tete = fileRequete;
		
		File nouveau = (File)malloc(sizeof(struct Req));
		nouveau->requete = x;
		nouveau->imprimante = p;
		nouveau->suivant = NULL;
		
		if (!EstVide())
		{
				while (tete->suivant!=NULL)
				{
					tete = tete->suivant;
				}
				tete->suivant = nouveau;
		}
		else
		{
				fileRequete = nouveau;
		}
		

		
} 	


/* --------------------------------------------------
 * Extraire
 * parametres : un entier x (resultat), un entier p (donné)
 * resultat : aucun
 * description :  supprime de la variable globale FileRequetes la requête la 
 * 			plus ancienne destinée à l'imprimante p
 * effet de bord : FileRequetes est modifiée
 ----------------------------------------------------- */

void Extraire (unsigned int *x, unsigned int p) 
{
		File tete = fileRequete;
		if (!EstVide())
		{
				if (tete->imprimante==p)
				{
					*x=tete->requete;
					fileRequete=fileRequete->suivant;
					free(tete);
				}
				else
				{
				
					while (tete->suivant!=NULL && (tete->suivant->imprimante!=p))
					{
							tete=tete->suivant;
					}
				
					if (tete->suivant!=NULL)
					{
							*x = tete->suivant->requete;
							File copie = tete->suivant;
							tete->suivant = tete->suivant->suivant;
							free(copie); 
					}
					else
					{
						*x = -1;
					}
				}
		}
		else
		{
				*x = -1;
		}
}

