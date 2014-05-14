#include <stdio.h>
#include "AA.h"
#include <ctype.h>

char *NomLex2string (NomLexeme n) {
   switch (n) {
      case NL : return "NL" ;
      case ETIQUETTE : return "ETIQUETTE" ;
      case NOM_REG : return "NOM_REG" ;
      case DIRECTIVE : return "DIRECTIVE" ;
      case INSTRUCTION : return "INSTRUCTION" ;
      case INTEGER : return "INTEGER" ;
      case CHAINE : return "CHAINE" ;
      case VIRGULE : return "VIRGULE" ;
      case POINT_EXCL : return "POINT_EXCL";
      case DIESE : return "DIESE";
      case MOINS : return "MOINS" ;
      case DEUX_POINTS : return "DEUX_POINTS" ;
      case PLUS : return "PLUS" ;
      case EGAL : return "EGAL" ;
      case PAR_OUV : return "PAR_OUV" ;
      case PAR_FERM : return "PAR_FERM" ;
      case ACCOL_OUV : return "ACCOL_OUV";
      case ACCOL_FERM : return "ACCOL_FERM";
      case CROCH_OUV : return "CROCH_OUV";
      case CROCH_FERM : return "CROCH_FERM";
      case ENDLEX : return "ENDLEX" ;
      case ERRLEX : return "ERRLEX" ;
      default :
           printf ("Oups! Internal error in NomLex2string\n");
           exit (1) ;
   }
}
static NomLexeme char2nat (char cc) {

   if  (cc == '\n') return NL ;
   if  (cc == ',') return VIRGULE ;
   if  (cc == '!') return POINT_EXCL ;
   if  (cc == '#') return DIESE ;
   if  (cc == '-') return MOINS ;
   if  (cc == ':') return DEUX_POINTS ;
   if  (cc == '+') return PLUS ;
   if  (cc == '=') return EGAL ;
   if  (cc == '(') return PAR_OUV ;
   if  (cc == ')') return PAR_FERM ;
   if  (cc == '{') return ACCOL_OUV ;
   if  (cc == '}') return ACCOL_FERM ;
   if  (cc == '[') return CROCH_OUV ;
   if  (cc == ']') return CROCH_FERM ;
   return ERRLEX ;
}
static int char2int (char cc) {
   if ((cc >= '0') && (cc <= '9'))
      return (int)cc - (int)'0' ;
   else 
      return (int)cc - (int)'A' + 10 ;
} 
static char *tableNomsRegs [] = {
   "r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8", "r9",
   "r10", "r11", "r12", "r13", "r14", "r15",
   "sp", "pc", "lr",
   ""
} ;

int EstNomReg (char *nom) {
   int i ;
   for (i = 0 ; ; i++) {
      if (!strcmp ("",  tableNomsRegs[i]))
         break ;
       if (!strcmp (nom, tableNomsRegs[i]))
         return 1 ;
   }
   return 0 ;
}
int LeNoReg (char *nom) {
int no;
   if (!strcmp (nom, "sp"))  no=13;
   else if (!strcmp (nom, "lr"))  no=14;
   else if (!strcmp (nom, "pc"))  no=15;
   else no=atoi(&nom[1]); /* on enleve le'r' de la chaine*/
return no;
}
static char *tableDirectives [] = {
   ".text",
   ".data",
   ".word",
   ".hword",
   ".byte",
   ".ascii",
   ".asciz",
   ".align",
   ".skip",
   ".global",
	".set",
   "LSL", "LSR", "ASR", "ROR", "RRX",
   ""
} ;

static char *tableInstructions1 [] = {
   "ADC",
   "ADD",
   "AND",
   "BIC",
   "EOR",
   "MLA",
   "MOV",
   "MUL",
   "MVN",
   "ORR",
   "RSB",
   "RSC",
   "SBC",
   "SMLAL",
   "SMULL",
   "SUB",
   "UMLAL",
   "UMULL",
   ""
} ;

static char *tableInstructions2 [] = {
   "B",
   "BL",
   "CLZ",
   "CMN",
   "CMP",
   "TEQ",
   ""
};
static char *tableConditions [] = {
   "EQ", "NE", "CS", "HS", "CC", "LO", "MI", "PL", "VS", "VC", "HI",
   "LS", "GE", "LT", "GT", "LE", "AL",
   ""
} ;

static char *tableGestionPile [] = {
   "IA", "IB", "DA", "DB", "FD", "FA", "ED", "EA",
   ""
};

int EstCondition (char *nom) {
   int i ;
   for (i = 0 ; ; i++) {
      if (!strcmp ("",  tableConditions[i]))
         break ;
       if (!strcmp (nom, tableConditions[i]))
         return 1 ;
   }
   return 0 ;
}

int EstGestionPile (char *nom) {
   int i ;
   for (i = 0 ; ; i++) {
      if (!strcmp ("",  tableGestionPile[i]))
         break ;
       if (!strcmp (nom, tableGestionPile[i]))
         return 1 ;
   }
   return 0 ;
}

int EstInstruction1 (char *nom) {
   int i ;
   for (i = 0 ; ; i++) {
      if (!strcmp ("",  tableInstructions1[i]))
         break ;
       if (!strcmp (nom, tableInstructions1[i]))
         return 1 ;
   }
   return 0 ;
}

int EstInstruction2 (char *nom) {
   int i ;
   for (i = 0 ; ; i++) {
      if (!strcmp ("",  tableInstructions2[i]))
         break ;
       if (!strcmp (nom, tableInstructions2[i]))
         return 1 ;
   }
   return 0 ;
}

/* MODIFS A&L dans ChercherMotCle */

int ChercherMotCle (Lexeme *lex) {
   char *nom ;
   int i ; int t;
   char sch[3]={'\0', '\0', '\0'} ; /* sous chaine pour stocker une indication de condition
                 ou de gestionpile eventuelle */
   char basech[5]; /* chaine pour stocker l'instruction de base eventuelle */

   nom = lex->chaine ;
   sch[0] = '\0' ; 

   /* Est-ce une directive ? */
   for (i = 0 ; ; i++) {
      if (!strcmp ("",  tableDirectives[i]))
         break ;
       if (!strcmp (nom, tableDirectives[i]))
	 { lex->nat = DIRECTIVE ; return 0 ; }
   }

   /* Est-ce un registre ? */
   if (EstNomReg(nom))
      {
      lex->nat = NOM_REG ;
      lex->noreg = LeNoReg (lex->chaine);
      return 0 ;
      }
   
   /* Est-ce une instruction ? */
   strcpy(lex->s_i.cond, "AL") ; /* on met la cond a AL par defaut */
   lex->s_i.BHW = 'W' ;   /*  autres vals par defaut */
   lex->s_i.S = 0 ;
   lex->s_i.T = 0 ;
   lex->s_i.cod_cond = 0 ; 
   lex->s_i.pile[0] = '\0' ;

   t = strlen (nom);

   basech[0] = nom[0]; basech[1] = nom[1];
   basech[2] = nom[2]; basech[3] = '\0';
   /* ----------------------------------------------------------- */
   if ((!strcmp (basech, "LDM")) || (!strcmp (basech, "STM"))) {
      strcpy(lex->s_i.base, basech) ;
   /* Est-ce une instruction LDM [cond] pile ou STM [cond] pile ? */
      if (t==5) {
         /* cas STM ou LDM avec indication gestion de pile ? */
         sch[0] = nom[t-2]; sch[1] = nom[t-1];
         if (EstGestionPile (sch)){
            lex->nat = INSTRUCTION ;
	    strcpy(lex->s_i.pile, sch) ;
	    return 0 ;
	    }
      }
      if (t==7) {
         /* cas STM ou LDM avec condition et indication de gestion de pile ? */
         sch[0] = nom[t-4]; sch[1] = nom[t-3];
         if (EstCondition (sch)) {
	    strcpy(lex->s_i.cond, sch) ;
            sch[0] = nom[t-2]; sch[1] = nom[t-1];
            if (EstGestionPile (sch)){
                lex->nat = INSTRUCTION ;
		strcpy(lex->s_i.pile, sch) ;
	        return 0 ;
	        }
         }
      }
   }
   /* ----------------------------------------------------------- */
	else if ((!strcmp (basech, "LDR")) || (!strcmp (basech, "STR"))){
         strcpy(lex->s_i.base, basech) ;
	/* Est-ce une instruction LDR [COND] (ou STR) suivie eventuellement
      de B, SB, H, SH, T, BT ? */
		if (t==3) {
        /* cas LDR ou STR sans rien derriere */
		  lex->nat = INSTRUCTION ;
		  return 0 ;
		}
		if (t==4) {
		  /* cas LDRB ou LDRH ou LDRT (id avec STR) */
		  if ( (nom[t-1]=='B') || (nom[t-1]=='H') || (nom[t-1]=='T') )
		     {
		     lex->nat = INSTRUCTION ;
		     switch (nom[t-1]) {
			case 'B' :  lex->s_i.BHW = 'B' ; break ; 
			case 'H' :  lex->s_i.BHW = 'H' ; break ;
			case 'T' :  lex->s_i.T = 1 ; break ;
			}	
		     return 0 ;
		     }
      }
		if (t==5) {
		  /* cas LDRcc ou LDRSB ou LDRSH ou LDRBT (id avec STR) */
        sch[0] = nom[t-2]; sch[1] = nom[t-1];
		    if ( EstCondition (sch)) {
				lex->nat = INSTRUCTION ;
				strcpy(lex->s_i.cond, sch) ;
				return 0 ;
				};
		    if (!strcmp (sch, "SB")) {
                               lex->nat = INSTRUCTION ;
                               lex->s_i.S = 1 ;
			       lex->s_i.BHW = 'B' ;
				return 0 ;
                                };
		    if (!strcmp (sch, "SH")) {
                               lex->nat = INSTRUCTION ;
                               lex->s_i.S = 1 ;
			       lex->s_i.BHW = 'H' ;
				return 0 ;
                                };
		    if (!strcmp (sch, "BT")) {
                               lex->nat = INSTRUCTION ;
                               lex->s_i.T = 1 ;
			       lex->s_i.BHW = 'B' ;
				return 0 ;
                                };
		}
		if (t==6) {
        /* cas LDRccB ou LDRccH ou LDRccT (id avec STR) */
		  sch[0] = nom[t-3]; sch[1] = nom[t-2];
		  if ( EstCondition (sch) &&
		       ( (nom[t-1]=='B') || (nom[t-1]=='H') || (nom[t-1]=='T') ) )
			{
			 lex->nat = INSTRUCTION ;
			 strcpy(lex->s_i.cond, sch) ;
                     	 switch (nom[t-1]) {                
                        	case 'B' :  lex->s_i.BHW = 'B' ; break ; 
                        	case 'H' :  lex->s_i.BHW = 'H' ; break ;
                        	case 'T' :  lex->s_i.T = 1 ; break ;
                        	}
		        return 0;
			}
		}
		if (t==7) {
        /* cas LDRccSB ou LDRccSH ou LDRccBT (id avec STR) */
		  sch[0] = nom[t-4]; sch[1] = nom[t-3];
		  if (EstCondition (sch)) {
		      strcpy(lex->s_i.cond, sch) ;
		      sch[0] = nom[t-2]; sch[1] = nom[t-1];
                      if (!strcmp (sch, "SB")) {
                               lex->nat = INSTRUCTION ;
                               lex->s_i.S = 1 ;
                               lex->s_i.BHW = 'B' ;
				return 0 ;
                                };
                      if (!strcmp (sch, "SH")) {
                               lex->nat = INSTRUCTION ;
                               lex->s_i.S = 1 ;
                               lex->s_i.BHW = 'H' ;
				return 0 ;
                                };
                      if (!strcmp (sch, "BT")) {
                               lex->nat = INSTRUCTION ;
                               lex->s_i.T = 1 ;
                               lex->s_i.BHW = 'B' ;
				return 0 ;
                                };
		  }
		}
	}
   /* ----------------------------------------------------------- */
	else if (!strcmp (basech, "SWP")) {
		strcpy(lex->s_i.base, basech) ;
	   /* Est-ce une instruction SWP [COND] [B] */
		if (t==3) {
        /* cas SWP sans rien derriere */
		  lex->nat = INSTRUCTION ;
	          return 0 ;
		}
		if (t==4) {
		   /* cas SWPB sans rien derriere */
			if ( nom[t-1]=='B' )
			{
			   lex->nat = INSTRUCTION ;
			   lex->s_i.BHW = 'B' ;
				return 0 ;
			}
		}
		if (t==5) {
		   /* cas SWPcc */
			sch[0] = nom[t-2]; sch[1] = nom[t-1];
			if ( EstCondition(sch) )
			{
			   lex->nat = INSTRUCTION ;
			   strcpy(lex->s_i.cond, sch) ;
				return 0 ;
			}
		}
		if (t==6) {
         /* cas SWPccB */
			sch[0] = nom[t-3]; sch[1] = nom[t-2];
			if ( EstCondition(sch) && (nom[t-1]=='B') )
			{
			    lex->nat = INSTRUCTION ;
			    lex->s_i.BHW = 'B' ;
			    strcpy(lex->s_i.cond, sch) ;
				return 0 ;
			}
		}
	}
   /* ----------------------------------------------------------- */
   else {
   /* ---------------------------------------------- */
   /* Est-ce une instruction de type 1 : base [cond] [S] */
   if (nom[t-1] == 'S') {
      /* il est possible que ce soit le S final
         on extrait les deux caracteres precedents
         qui peuvent etre une condition */
      sch[0] = nom[t-3]; sch[1] = nom[t-2];
      if (EstCondition (sch)) {
         strncpy (basech, nom, t-3);
         basech[t-3] = '\0';
         if (EstInstruction1 (basech))
	   {
           lex->nat = INSTRUCTION ;
	   strcpy(lex->s_i.base, basech) ;
	   strcpy(lex->s_i.cond, sch) ;
	   lex->s_i.cod_cond = 1;
				return 0 ;
	   }
      }
      else {
        /* instruction sans condition ? */
         strncpy (basech, nom, t-1);
         basech[t-1] = '\0';
         if (EstInstruction1 (basech))
          {
           lex->nat = INSTRUCTION ;
           strcpy(lex->s_i.base, basech) ;
           lex->s_i.cod_cond = 1;
				return 0 ;
           }

      }
   }
   /* pas de S a la fin 
      il peut y avoir une indication de condition */
   sch[0] = nom[t-2]; sch[1] = nom[t-1];
   if (EstCondition (sch)) {
      strncpy (basech, nom, t-2);
      basech[t-2] = '\0';
      if (EstInstruction1 (basech))
           {
           lex->nat = INSTRUCTION ;
           strcpy(lex->s_i.base, basech) ;
           strcpy(lex->s_i.cond, sch) ;
				return 0 ;
           }

   }
   /* pas de S a la fin, pas de condition */
   if (EstInstruction1 (nom))
	 {
         lex->nat = INSTRUCTION ;
	 strcpy(lex->s_i.base, basech) ;
				return 0 ;
	 }

   /* ---------------------------------------------- */
   /* Est-ce une instruction de type 2 : base [cond] */
   sch[0] = nom[t-2]; sch[1] = nom[t-1];
   if (EstCondition (sch)) {
      strncpy (basech, nom, t-2);
      basech[t-2] = '\0';
      if (EstInstruction2 (basech))
           {
           lex->nat = INSTRUCTION ;
           strcpy(lex->s_i.base, basech) ;
           strcpy(lex->s_i.cond, sch) ;
				return 0 ;
           }

   }
   /* pas de condition */
   if (EstInstruction2 (nom))
         {
         lex->nat = INSTRUCTION ;
         strcpy(lex->s_i.base, basech) ;
				return 0 ;
         }
   }
   /* cela ne peut plus etre qu'une etiquette */
   lex->nat = ETIQUETTE ; 
   return 0 ;
}
#include <stdio.h>
#define              TAILLE_TAS_CHAR      10000

static FILE         *leFichier ; 
static Lexeme        leLex ; /* en cours de constrution */
static char          taschar [TAILLE_TAS_CHAR] ;
static int           nol, noc ;
static int           cc ; /* caractere courant */
static char         *ptaschar ; /*premiere case libre dans le tas de caracteres */

/* Codage des états de l'automate */
typedef enum {
   E_INIT, E_CHAINE, E_ERREUR, E_INTEGER, 
   E_IDF_KEYW, E_COMM, E_TERM,
   E_VERIF_NOTA_HEXA,
   E_INTEGER_HEXA
} Etat ;

static int mygetc (FILE *fp) {
    int c ; 
   c = getc (fp) ;
   if (c == '\n') {
      nol ++ ;
       noc = 0 ; 
   }
   else {
       noc++ ;
   }
   /* printf ("               car : [%c] %d %d\n", c, nol, noc) ; */
   return c ;
}
void    DemLex (FILE *fpin) {
   /* fpin est un fichier qui a été ouvert correctement */
   leFichier = fpin ;   
   nol       = 1 ;
    noc       = 0 ; 
    ptaschar  = taschar ;

    cc        = mygetc(leFichier) ;
   AvLex () ; 
}


void    AvLex () {
    Etat ee = E_INIT ; /* etat courant */
    int  a_consommer ; /* faut-il consommer le caractere ? */
   int  value       ; /* valeur entiere si lexeme INTEGER */

   while ((cc != EOF) && (ee != E_ERREUR) && (ee != E_TERM)) {
        a_consommer = 1 ; /* a priori, il faut consommer */
       switch (ee) {
         case E_INIT : 
            
{
if      (cc == '@')  ee = E_COMM;
else if ((cc == ' ') || (cc == '\t')) { ; } 
else if (isdigit(cc) && (cc != '0')) {
      ee         = E_INTEGER ; 
      leLex.nat  = INTEGER ;
      value      = char2int (cc) ;
      *ptaschar  = cc ;
      leLex.chaine = ptaschar ;
      leLex.nol    = nol ;
      leLex.noc    = noc ;
      ptaschar++;
}
else if (cc == '0') {
      ee           = E_VERIF_NOTA_HEXA ;
      leLex.nat    = INTEGER ;      
       value        = 0 ;
      leLex.chaine = ptaschar ;
      leLex.nol    = nol ;
      leLex.noc    = noc ;
}
else if (isalpha(cc) || (cc == '_') || (cc=='.') ) {
      ee    = E_IDF_KEYW ;
      *ptaschar = cc ;
       /* leLex.nat encore inconnu mais on met ETIQUETTE a priori */
      leLex.nat = ETIQUETTE ;
      leLex.chaine = ptaschar ;
      ptaschar++;
      leLex.nol    = nol ;
      leLex.noc    = noc ;
}
else if (cc =='"') {
   ee = E_CHAINE ;
   *ptaschar = cc ;
   leLex.chaine = ptaschar ;
   ptaschar++;
   leLex.nat    = CHAINE ;
   leLex.nol    = nol ;
   leLex.noc    = noc ;
}
else if ((cc == ',') || (cc == '!') || (cc == '{') || (cc == '}') ||
         (cc == '[') || (cc == ']') || (cc == '#') || (cc == '^') ||
         (cc == '-') || (cc == '(') || (cc == ')') ||
         (cc == '+') || (cc == '=') || (cc == ':') ||
         (cc == '\n'))  { 
      ee = E_TERM ;
      *ptaschar = cc ;
      leLex.chaine = ptaschar ;
      ptaschar++;
      leLex.nat = char2nat (cc) ;
      leLex.nol    = nol ;
      leLex.noc    = noc ;
}
else {
      leLex.nat = ERRLEX ;
       ee         = E_ERREUR ;
      leLex.nol    = nol ;
      leLex.noc    = noc ;
      *ptaschar = cc ;
      leLex.chaine = ptaschar ;
      ptaschar++;
}
}
            break ;
         case E_CHAINE :
            
*ptaschar = cc ;
ptaschar++;
if (cc == '"') ee = E_TERM ;   
            break ;
         case E_COMM :
            
if (cc == '\n') {
      ee = E_TERM ;
      *ptaschar = cc ;
      leLex.chaine = ptaschar ;
      ptaschar++;
      leLex.nat = char2nat (cc) ;
      leLex.nol    = nol ;
      leLex.noc    = noc ;
}
            break ;
         case E_INTEGER :
            
if (isdigit (cc) ) {
   value = 10*value + char2int (cc) ;
   *ptaschar = cc ; ptaschar++   ;
}
else {
   a_consommer = 0 ;
   ee = E_TERM ; 
   leLex.value = value ;
}
            break ;
         case E_IDF_KEYW :
            
if (isdigit(cc) || isalpha(cc) || (cc == '_') ) {
   *ptaschar = cc ; ptaschar++   ;
}
else {
   a_consommer = 0 ;
   ee = E_TERM ; 
}   
            break ;
         case E_VERIF_NOTA_HEXA :
            
if (cc == 'x') {
   ee = E_INTEGER_HEXA ;
}
else if (isdigit (cc)) {
   ee = E_INTEGER ;
   a_consommer = 0 ;
}
else {
   ee = E_TERM ; 
   a_consommer = 0 ;
   leLex.value = value ; /* 0, normalement */   
}
            break ; 
         case E_INTEGER_HEXA : 
            
if (isdigit (cc) || (cc == 'A') || (cc == 'B') || (cc == 'C') ||
                 (cc == 'D') || (cc == 'E') || (cc == 'F') ||
               (cc == 'a') || (cc == 'b') || (cc == 'c') ||
               (cc == 'd') || (cc == 'e') || (cc == 'f')) {
   value = 16*value + char2int (cc) ;
   *ptaschar = cc ; ptaschar++   ;
}
else {
   a_consommer = 0 ;
   ee = E_TERM ; 
   leLex.value = value ;
}
            break ; 
         default :
               printf ("Oups! Internal error in AvLex\n");
               exit (1) ;
        }
       if (a_consommer) cc = mygetc (leFichier) ; 
    }

   /* terminer la chaine lue */
   *ptaschar = '\0' ; ptaschar++ ;

   /* On a atteint un état terminal, ou l'état d'erreur, ou alors la
   fin de fichier. Une analyse par cas est nécessaire. 
   */ 
   
if (ee == E_ERREUR)  {
   /* rien a faire de plus.  */
}
else if (ee == E_TERM) {
   /* on a termine un lexeme proprement.
      il se peut qu'on vienne de reconnaitre un mot, il faut
      determiner de quelle espece de lexeme il s'agit.  */
   if (leLex.nat == ETIQUETTE) {
         /* finir le travail */
	ChercherMotCle(&leLex) ;
   }
   /* sinon le lexeme est entierement construit. */
}
else /* cad (cc == EOF) && (ee != E_ERREUR) & (ee != E_TERM) */ {
   /* on n'a pas le droit de finir le fichier dans n'importe quel etat :
    */
   if ((ee == E_COMM) || (ee == E_CHAINE)) {
      leLex.nat = ERRLEX ;
   }
   else {
      /* ici ee=E_INIT ou E_INTEGER ou E_IDF_KEYW
         si E_INIT, on avait des espaces avant la fin de fichier.
          si E_INTEGER, on a trouve EOF juste derriere un nb, finir le travail
           si E_IDF_KEYW, on a trouve EOF juste derriere un mot, finir le travail
      */
      if (ee == E_INIT)    leLex.nat = ENDLEX ;
      if (ee == E_INTEGER) leLex.value = value ;
      if (ee == E_IDF_KEYW) {
        ChercherMotCle(&leLex) ;
       }
   }
}

   
}
Lexeme  LexCour () {
   return leLex ;
}
int     FinLex  () {
    return leLex.nat == ENDLEX ;

}
