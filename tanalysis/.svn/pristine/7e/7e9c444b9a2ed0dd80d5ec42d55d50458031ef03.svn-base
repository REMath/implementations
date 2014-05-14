#include "Occ.h"


int main (int argc, char *argv[]){
		
	FILE *fichier;
	codeCar tabOcc[MAX];
	
	if(argc != 3)
	{
		printf("error nb arg\n");
		exit(1);	
	}
			
	fichier = fopen(argv[1], "r");
	if (fichier == NULL)		
	{
		printf("error to open file\n");
		exit(1);	
	}
	
	initTab(tabOcc);
	countOcc(fichier, tabOcc);
	
	Arbre arbreHuff;
	arbreHuff = huff(tabOcc);
	length(arbreHuff, tabOcc);
	afficheTab(tabOcc);
	
	// Ouverture du fichier ou l'on mettrat le code 
	// Remarque : la fichier doit etre pret exitant
	FILE *fichierCode;
	fichierCode = fopen(argv[2], "w");
	if (fichier == NULL)		
	{
		printf("error to open file\n");
		exit(1);	
	}
	
	ecritureFichierCode(fichierCode, tabOcc);
	
	fclose(fichier);
	fclose(fichierCode);
	return 0;
}







