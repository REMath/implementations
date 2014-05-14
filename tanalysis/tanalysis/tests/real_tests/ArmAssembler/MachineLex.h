#include <stdio.h>

/* Type énuméré pour coder toutes les espèces de lexèmes
   du langage étudié. On ajoute ENDLEX pour traiter facilement
   la fin de fichier, et ERRLEX en cas de caractère non
   reconnaissable. 
*/
typedef enum   { NL, ETIQUETTE, NOM_REG, DIRECTIVE, INSTRUCTION, INTEGER,
                CHAINE, VIRGULE, POINT_EXCL, DIESE, MOINS, DEUX_POINTS,
                PLUS, EGAL,
                PAR_OUV, PAR_FERM, ACCOL_OUV, ACCOL_FERM,
                CROCH_OUV, CROCH_FERM, ENDLEX,ERRLEX }  NomLexeme ;

/* Un lexème est constitué d'un nom de lexème, de la 
   sous-chaîne de caractères extraite du fichier source,
   et des infos de retour au source (nos de ligne et colonne).
 */


typedef struct {
        char base[6] ;                  /* base du mnemo */
        char cond[3] ;                  /* condition */
        int cod_cond ;                  /* bit S = maj des codes cond. */
        char BHW ;                      /* taille pour LDR et STR */
        int S ;                         /* signe pour LDR et STR */
        int T ;                         /* translation pour LDR et STR */
        char pile[3] ;                  /* param de pile pour STM et LDM */
} champs_inst ;

typedef struct {
        NomLexeme nat ;
       char     *chaine ; 
       int       nol, noc ;
       int       value ; /* utilise pour les INTEGER */
       int       noreg ; /* utilise pour les NOMREG */
		                   /* on garde le numéro du registre */
       champs_inst s_i ;  /* utilise pour les INSTRUCTION */
} Lexeme ;


void    DemLex (FILE *fpin)
{
}

void    AvLex ()
{
}

Lexeme  LexCour ()
{
    Lexeme l;
    return l;
}
int     FinLex  ()
{
    return 0;
}