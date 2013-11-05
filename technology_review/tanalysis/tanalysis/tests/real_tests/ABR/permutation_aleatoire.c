#include <stdio.h>

static unsigned int x ; /* terme precedent de la suite aleatoire */
static unsigned int val_max ; /* intervalle de generation = [0,val_max[ */

void init_alea (unsigned int germe, unsigned int n) {
	x = germe ;
	val_max = n;
}


static unsigned int suivant_alea()
{
    unsigned int y ;

    y = x*1103515245 + 12345 ;
    x = y ;
    y = y & 0xfffffff ;
        /* la constante hexadecimale 0xfffffff = 2^28 - 1       */
        /* on "masque" le premier chiffre hexadecimal de z      */
        /* c'est-a-dire les 4 premiers chiffres binaires        */
    y = y / 0x1000 ;
        /* division entiere par 0x1000, soit 2^12 = 4096          */
        /* on supprime les 3 derniers chiffres hexadecimaux de z  */
        /* c'est-a-dire les 12 derniers chiffres binaires         */
   return (y % val_max) ;
}


static void rand_fact (int t_fact[], int n) {

	int i ;

	t_fact[0] = 0 ;
	for (i=1 ; i<n ; i++)
		t_fact[i] = (int) (suivant_alea() % (i+1)) ;
}

static void fact_to_perm(int t_fact[], int n, int t[]) {

int i, place, j, nb_libre ;
int marque[n] ;

	for (i=0 ; i<n ; i++) 
		marque[i] = 0 ;

	for (i=n-1 ; i>=0 ; i--) {
		place = t_fact[i] ;
		nb_libre = -1 ; j = -1 ;
	        while (nb_libre < place) {
			j = j+1 ;
			if (!marque[j]) 
				nb_libre = nb_libre+1 ;
		} ;
		t[j] = i ;
		marque[j] = 1 ;
	} ;	
}

void permutation_aleatoire (int t[], int n)
{
	int t_fact[n] ;

	rand_fact (t_fact, n) ;
	fact_to_perm (t_fact, n, t) ;
}


void affiche_permutation (int T[], int n) {
  	int i ;

  	printf("[") ;
  	for (i = 0 ; i < n ; i++) {
        	printf (" %d ", T[i]) ;
  	}
  	printf("]\n") ;
}


