#include "Occ.h"


void length(Arbre huff, codeCar cc[])
{
	int i;
	int hauteur =0;
	int code = 0;
	for (i=0;i<MAX;i++)
	{
		cc[i].codeLength = 0;
		cc[i].codage = 0;
	}
	longCode(huff,&code, cc, &hauteur);
}


codeCar *longCode (Arbre huff,int *code, codeCar CC[], int *hauteur){
	
	
	if(!EstVide(huff)){
		if(EstFeuille(huff)){
			CC[Car(huff)].codeLength = *hauteur;
			CC[Car(huff)].codage = *code;		
			return CC;
		}
		
		
		if(!EstVide(FilsGauche(huff))){
			(*hauteur)++;
			longCode(FilsGauche(huff),&(*code), CC, &(*hauteur));
			(*hauteur)--;
		}
		if(!EstVide(FilsDroit(huff))){
			(*hauteur)++;
			int t = *code;
			int tmp = 0;
			tmp =  1 << (*hauteur);
			*code= *code | tmp;
			longCode(FilsDroit(huff),&(*code), CC, &(*hauteur));
			(*hauteur)--;
			*code = t;
		}
		

	}
	return CC;

}

void _bitread(int code, int length){
	int i;
	for (i=length; i>0;i--)
		{			
			printf("%d",(code >> i) & 1);
		}
}

void initTab(codeCar cc[]){
	int i;
	for(i = 0; i < MAX; i++)
		cc[i].occur = 0;
	
}

void countOcc (FILE *fichier, codeCar tabOcc[]){
	char c;
	while (!feof(fichier)) {
		fscanf(fichier, "%c", &c) ;
		tabOcc[(int) c].occur++;
	}
  
}

void afficheTab(codeCar cc[]){
	int i;
	for(i = 0; i < MAX; i++){
		if(cc[i].occur != 0){
			printf("%c %d  %d %d\n", (char) i, cc[i].occur, cc[i].codeLength, cc[i].codage);
			_bitread(cc[i].codage,cc[i].codeLength);
			printf("\n");
		}
	}
}

Arbre huff (codeCar tabOcc[]){
	int i;
	Arbre arbre;
	int nbCar = 0;
	fap fapOcc = creer_fap_vide();
	for(i = 0; i < MAX; i++){
		if(tabOcc[i].occur != 0){
			Arbre arbreT = Cons(tabOcc[i].occur, i, NULL, NULL) ;
			fapOcc = inserer(fapOcc, arbreT, tabOcc[i].occur);	
			nbCar++;
		}
	}
	
	for(i = 0; i < (nbCar - 1); i++){
		Arbre arbreT;
		Arbre fd;
		Arbre fg;
		int poidD;
		int poidG;
		fapOcc = extraire(fapOcc, &fg, &poidG);
		fapOcc = extraire(fapOcc, &fd, &poidD);
		arbreT = Cons(poidD + poidG, -1, fg, fd) ;
		fapOcc = inserer(fapOcc, arbreT, poidD + poidG);
	}
	int poid;
	fapOcc = extraire(fapOcc, &arbre, &poid);
	
	return arbre;
}

int nbCarDiff (codeCar *codeC){
	int i, res = 0;
	for(i = 0; i < MAX; i++){
		if(codeC[i].occur != 0){
			res++;
		}

	}
	return res;
}

int sizeHuff (codeCar tabOcc[]){
	int i, res = 0;
	for(i = 0; i < MAX; i++){
		res += tabOcc[i].occur * tabOcc[i].codeLength;
	}
	return res;
}

void ecritureFichierCode(FILE *fichierCode, codeCar *tabOcc){
	
	int i, j;
	// ecriture de la table de codage
	// mais dabord le nombre de caracteres dans la table a encoder
	int nbCarDiffC = nbCarDiff(tabOcc);
	for(j = 0; j < (sizeof(int) / sizeof(char)); j++){
			fputc(nbCarDiffC, fichierCode);
			nbCarDiffC = nbCarDiffC >> 8;	//decalage d'un octet 
	}
					
	// ecriture des caracteres suivis de leur codage et de la taille du code
	for(i = 0; i < MAX; i++){
		if(tabOcc[i].occur != 0){
			// Ecrire Lettre
			fputc(tabOcc[i].caractere, fichierCode);
			//ecrire code
			int code = tabOcc[i].codage;
			// ecriture des 4 octets du code
			for(j = 0; j < (sizeof(int) / sizeof(char)); j++){
					fputc(code, fichierCode);
					code = code >> 8;	//decalage d'un octet 
			}
			
			// ecriture de la taille du code
			int codeL = tabOcc[i].codeLength;
			// ecriture des 4 octets
			for(j = 0; j < (sizeof(int) / sizeof(char)); j++){
					fputc(codeL, fichierCode);
					code = codeL >> 8;	//decalage d'un octet 
			}
		}
	}
	// ecriture du nombre de bit du fichier code
	int sizeCodeHuff = sizeHuff(tabOcc);
	for(j = 0; j < (sizeof(int) / sizeof(char)); j++){
			fputc(sizeCodeHuff, fichierCode);
			sizeCodeHuff = sizeCodeHuff >> 8;	//decalage d'un octet 
	}
	
	
	// ecriture du fichier code
	//ecrireCodeBinaire(tabOcc);
	
}

