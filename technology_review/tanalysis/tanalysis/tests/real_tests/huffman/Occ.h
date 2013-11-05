#include <stdio.h>
#include <stdlib.h>
#include "fap.h"
#include "arbre.h"

#define	MAX 256

typedef struct Codage_char {
	char caractere;
	int occur;
	int codeLength;
	int codage;
	} codeCar;

void initTab(codeCar tab[]);

void countOcc (FILE *fichier, codeCar tabOcc[]);

void afficheTab(codeCar tab[]);

Arbre huff (codeCar tabOcc[]);

codeCar *longCode (Arbre huff,int *code, codeCar tabLg[], int *hauteur);

void length(Arbre huff, codeCar cc[]);

int *constTabLgCode (Arbre huff, int tabLg[]);

int nbCarDiff (codeCar *codeC);

int sizeHuff (codeCar tabOcc[]);

void ecritureFichierCode(FILE *fichierCode, codeCar *tabOcc);


