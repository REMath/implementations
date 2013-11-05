#include <stdio.h> 
#include "AA.h"
static Elem LeProg[MAX_LIGNE_LOG] ;
static int nbLigneLog ;

/* Pré-déclaration des fonctions d'affichage de la structure de données */
static DumpParamExp (ParamExp) ;
static DumpExpImmEtiq (ExpImmEtiq) ;
static DumpParamInstShift (ParamInstShift) ;
static DumpParamInst (ParamInst) ;
static DumpParamReserv (ParamReserv) ;
void DumpSdd (Elem *, int) ;


static char *NatLigneLog2String (NatLigneLog nat) {
   switch (nat) {
      case LL_ETIQ          : return "LL_ETIQ "  ;
      case LL_INST          : return "LL_INST "  ;
      case LL_CTE           : return "LL_CTE " ;
      case LL_SECT          : return "LL_SECT "  ;
      case LL_EXPORT        : return "LL_EXPORT "  ;
      case LL_RESERV_INIT   : return "LL_RESERV_INIT "  ;
      case LL_RESERV_N_INIT : return "LL_RESERV_N_INIT "  ; /* skip */
      case LL_ALIGN         : return "LL_ALIGN "  ;
      case LL_NONE          : return "LL_NONE "  ;
      default :
           printf ("Oups! Internal error in NatLigneLog2String\n");
           exit (1) ;
   }
}

extern char *NomZone2String (NomZone n) {
   switch (n) {
      case Z_TEXT  : return "TEXT"  ;
      case Z_DATA  : return "DATA"  ;
      case Z_BSS   : return "BSS"  ;
      case Z_NONE  : return "UNDF"  ;
      default :
           printf ("Oups! Internal error in NomZone2String\n");
           exit (1) ;
   }
}

static char *DirReserv2Char (DirReserv d) {

   switch (d) {
      case R_WORD  : return "word" ;
      case R_HALF  : return "half" ;
      case R_BYTE  : return "byte" ;
      case R_ASCIZ  : return "asciz" ;
      case R_ASCII  : return "ascii" ;
      case R_INT    : return "int" ;
      case R_ETIQ   : return "etiq" ;
      default :
           printf ("Oups! Internal error in DirReserv2Char\n");
           exit (1) ;
   }
}

static char *NatParamInst2String (NatParamInst nat) {
   switch (nat) {
      case P_IMMEDIAT       : return "P_IMMEDIAT"  ;
      case P_EXP            : return "P_EXP" ;
      case P_NOMREG         : return "P_NOMREG"  ;
      case P_NOMREG_EXCL    : return "P_NOMREG_EXCL"  ;
      case P_ETIQUETTE      : return "P_ETIQUETTE"  ;
      case P_INDIR          : return "P_INDIR"  ;
      case P_SHIFT          : return "P_SHIFT" ;
      case P_REGS           : return "P_REGS" ;
      default :
           printf ("Oups! Internal error in NatParamInst2String\n");
           exit (1) ;
   }
}

/* DumpParamExp
 * - Impression d'un parametre d'instruction de la forme expression
 * PARAM : l'expression
*/
static DumpParamExp (ParamExp p) {
int i;
    printf (" %s ", NatParamInst2String (p.nat));
    switch (p.nat) {
    case P_IMMEDIAT :
       printf ("%5d ", p.valimm);
       break;
    case P_ETIQUETTE :
       printf ("%15s ", p.nom_etiq);
       break;
    case P_EXP :
       /* l'expression est de la forme (e1 - e2 - e3 -...) */
       printf ("(");
       for (i=0 ; i<(p.nbexp); i++) {
           DumpExpImmEtiq ( (p.tabexp)[i] );
           printf (" - ");   /* il y aura un moins de trop a la fin, pas grave... */
       }
       printf (")");
       break;
    default :
           printf ("Oups! Internal error in DumpParamExp\n");
           exit (1) ;
    }
}

/* DumpExpImmEtiq
 * - Impression d'une expression immediate ou etiquette
 * PARAM : l'expression
*/
static DumpExpImmEtiq (ExpImmEtiq exp) {
   switch (exp.nat) {
   case P_IMMEDIAT :
       printf ("%d", exp.valimm);
       break;
   case P_ETIQUETTE :
       printf ("%s", exp.nom_etiq);
       break;
   default :
           printf ("Oups! Internal error in DumpExpImmEtiq\n");
           exit (1) ;
   }
}

/* DumpParamInstShift
 * - Impression d'un paramètre d'instruction de la forme shift expression
 * PARAM : le parametre
*/
static DumpParamInstShift (ParamInstShift p) {
   printf(" %s ", p.dir_shift);
   if (strcmp(p.dir_shift, "RRX")) {
      if (p.nat==P_NOMREG) printf (" r%d ", p.noregshift);
      else /* p.nat==P_IMMEDIAT */ printf (" %d ", p.valimmshift);
   }
}

/* DumpParamInst
 * - Impression d'un parametre d'instruction
 * PARAM : le parametre
 */
static DumpParamInst (ParamInst p) {
int i;

   printf (" %10s ", NatParamInst2String (p.nat)) ;

   switch (p.nat) {
      case P_EXP :
         DumpParamExp (p.u.exp);
         break ;
      case P_NOMREG :
      case P_NOMREG_EXCL :
         printf ("r%d ", p.u.noreg) ;
         if (p.nat==P_NOMREG_EXCL) printf (" ! ");
         break ;
      case P_INDIR : 
         printf ("[") ; 
         if (p.u.indir.nbelt >= 1) printf ("r%d", p.u.indir.noreg1) ; 
         if (p.u.indir.nbelt == 2)
            switch (p.u.indir.nat) {
            case IND_EXP :
                 printf (", ");
                 DumpParamExp (p.u.indir.exp);
                 break;
            case IND_NOMREG :
            case IND_NOMREG_SHIFT :
                 if (p.u.indir.signe==S_MOINS)
                      printf (", -r%d", p.u.indir.noreg2) ;
                 else printf (", r%d", p.u.indir.noreg2) ;
                 if (p.u.indir.nat==IND_NOMREG_SHIFT)
                     DumpParamInstShift (p.u.indir.exp_shift);
                 break;
            }
         printf (" ] ");
         break ;
      case P_REGS :
         printf ("{") ;
         for (i=0; i<=16; i++)
             if (p.u.regs[i] == 1)
                printf ("r%d, ", i);
         printf ("}") ;
         /* y aura une virgule de trop mais pour l'instant ce n'est
            pas tres important */
         break;
      case P_SHIFT :
         DumpParamInstShift (p.u.exp_shift);
         break;
      default :
           printf ("Oups! Internal error in DumpParamInst\n");
           exit (1) ;
   }
}

/* DumpParamReserv
 * - Impression d'un paramètre de reservation de donnée initilisée
 * PARAM : le paramètre
*/
static DumpParamReserv (ParamReserv p) {
   switch (p.nat) {
   case PR_CHAINE :
      printf ("%s", p.chaine);
      break;
   case PR_NOMBRE :
      printf ("%d", p.nb);
      break;
   case PR_ETIQUETTE :
      printf ("%s", p.nom_etiq);
      break;
   default :
           printf ("Oups! Internal error in DumpParamReserv\n");
           exit (1) ;
   }
}

/* DumpSplitInst
 * Impression des champs du mnemo de l'instruction
 */
static void DumpSplitInst(champs_inst s_i) {
printf(" %5s-%2s-%1d-%c-%1d-%1d-%2s ", s_i.base, s_i.cond, s_i.cod_cond, 
				s_i.BHW, s_i.S, s_i.T, s_i.pile) ;
}

/* DumpSdd 
 * - Impression de toutes les structures de donnees.
 * PARAM : LeProg : adresse du tableau a imprimer
 * PARAM : nbLigneLog : nb de lignes 
 */
void DumpSdd (Elem *LeProg, int nbLigneLog) {
int i, p ;

printf("|     |     |     |    |\n") ;
printf("|No_lg|ZONE |@dsZ |taye|nature ligne ... \n") ;

   for (i = 0 ; i < nbLigneLog ; i++) {
      LigneLog L = LeProg[i].ligne ;   
      printf ("|%4d ", LeProg[i].nl_source);
      printf("|%s ", NomZone2String(LeProg[i].zone_cour)) ;
      printf("|%4d ", LeProg[i].ad_dans_zone) ;
      printf("| %2d ", LeProg[i].nb_bits) ;
      printf ("|%15s ", NatLigneLog2String(L.nat));
      
      switch (L.nat) {
         case LL_ETIQ         : 
            printf ("%10s ", L.u.nom_etiq);
            break ;
         case LL_CTE  :
            printf ("%10s ", L.u.cte.etiq);
            printf ("%d", L.u.cte.valcte);
            break ;
         case LL_INST            :
            printf ("%10s ", L.u.uinst.mnemo);
	    DumpSplitInst(L.u.uinst.s_i) ;
	    for (p=0 ; p<L.u.uinst.nbp ; p++) {
               DumpParamInst (L.u.uinst.p[p]) ;
               printf (", ");
	    } ;
            break  ;
         case LL_EXPORT         : 
            printf (" %10s ", L.u.nom_globl);
            break  ;
         case LL_SECT          : 
            printf ("%s ", NomZone2String (L.u.sect)) ;   
            break   ;
         case LL_RESERV_N_INIT        :
            /* reservation sans initialisation */
            if (L.u.urni.dir == R_INT)
               printf ("%10d  ", L.u.urni.nboctets);
            else /* L.u.urni.dir == R_ETIQ */
               printf ("%s", L.u.urni.etiq);
            break  ; 
         case LL_RESERV_INIT   : 
            printf ("%s ", DirReserv2Char(L.u.uri.dir)) ;
            DumpParamReserv (L.u.uri.p0) ;
            break  ;
         case LL_ALIGN         : 
            printf ("%10d  ", L.u.align);
            break  ;
         case LL_NONE          : break ;
         default :
              printf ("Oups! Internal error in DumpSdd\n");
              exit (1) ;
      }
        
      printf ("\n");   
   }
}

/* Les codes d'erreur 
 */
typedef enum { 
    NOERR,
   FIN_LIGNE, 
   DEB_LIGNE,
   ERR_LEX,
   INT_ATTENDU,
   INT_ALIGN_ATTENDU,
   CHAINE_ATTENDUE,
   VIRGULE_ATTENDUE,
   TROP_PARAM_INST,
   ZERO_PARAM_INST,
   NB_ETIQ_ATTENDUS,
   PAROUV_ATTENDUE,
   PARFERM_ATTENDUE,
   DIRECTIVE_ATTENDUE,
   DIRECTIVE_INCONNUE,
   NOM_REG_ATTENDU,
   ETIQUETTE_ATTENDUE,
   INSTRUCTION_ATTENDUE,
   MOINS_ATTENDU,
   INT_OU_ETIQ_ATTENDU,
   DIESE_PLUS_MOINS_REG,
   DIR_SHIFT_ATTENDUE,
   TROP_EXP,
   DEB_PARAM_INST,
   DEB_EXPRESSION,
   NO_END,
   DEUXPOINTS_ATTENDU,
   ACCOLFERM_ATTENDUE,
   CROCHFERM_ATTENDU
} CodeErreur ; 

/* forme imprimable des messages d'erreur 
 */
static char * CodeErreur2String (CodeErreur c) {
    switch (c) {
   case NOERR              :  return "" ;
   case FIN_LIGNE          :  return "Il manque un saut de ligne" ;
   case DEB_LIGNE          :  return "Mauvais debut de ligne" ;
   case ERR_LEX            :  return "Lexeme inconnu" ;
   case INT_ATTENDU        :  return "Entier attendu" ;
   case INT_ALIGN_ATTENDU  :  return "1, 2, 4 ou 8 attendu comme paramètre de .align" ;
   case CHAINE_ATTENDUE    :  return "chaîne de caractères attendue" ;
    case VIRGULE_ATTENDUE   :  return "virgule attendue" ;
   case TROP_PARAM_INST    :  return "une instruction ne peut pas avoir plus de 3 parametres" ;
   case ZERO_PARAM_INST    :  return "une instruction doit avoir au moins 1 parametre" ;
   case NB_ETIQ_ATTENDUS   :  return "Nombre ou etiquette attendus" ;
   case PAROUV_ATTENDUE    :  return "parenthese ouvrante attendue" ;
   case PARFERM_ATTENDUE   :  return "parenthese fermante attendue" ;
	case DIRECTIVE_ATTENDUE :  return "directive attendue" ;
	case DIRECTIVE_INCONNUE :  return "directive inconnue" ;
   case ETIQUETTE_ATTENDUE :  return "etiquette attendue" ;
   case NOM_REG_ATTENDU    :  return "nom de registre attendu" ;
   case INT_OU_ETIQ_ATTENDU:  return "entier ou symbole attendu" ;
   case DIESE_PLUS_MOINS_REG : return "diese ou (+/-)registre attendu" ;
   case DIR_SHIFT_ATTENDUE :  return "directive lsl, lsr, asr, ror ou rrx attendue" ;
   case TROP_EXP           :  return "trop d'expressions dans une liste d'expressions" ;
	case DEB_PARAM_INST     :  return "debut de parametre d'instruction incorrect" ;
	case DEB_EXPRESSION     : return "entier, etiquette, +, - ou ( attendu" ;
   case NO_END             : return "directive END attendue" ;
   case DEUXPOINTS_ATTENDU : return "':' attendu" ;
   case ACCOLFERM_ATTENDUE : return "'}' attendu" ;
   case CROCHFERM_ATTENDU : return "']' attendu" ;
   default :
        printf("Oups! Internal error in CodeErreur2String\n");
        exit (1) ;
 }
}


/* ErreurSynt 
 *  - Impression d'un message d'erreur et exit 
 *  PARAM  c : le code erreur 
 *  PARAM  L : le lexeme le plus proche de l'erreur
 */
void ErreurSynt (CodeErreur c, Lexeme L) {
     printf("Erreur : %s -- pres du lexeme ligne %d, colonne %d\n", 
                CodeErreur2String(c),
                     L.nol, L.noc) ;
     exit (1) ;
}

/*  CodeDeLexAttendu
 *   - correspondance entre lexeme L  et code d'erreur pour
 *   - l'erreur `` L attendu''
 *   PARAM n : la nature de lexeme 
 *   RESULT  : le code d'erreur correspondant
 */

static CodeErreur CodeDeLexAttendu (NomLexeme n) {
   switch (n) {
    case  NL        : return FIN_LIGNE ; 
    case  ETIQUETTE : return ETIQUETTE_ATTENDUE ; 
    case  NOM_REG   : return NOM_REG_ATTENDU ;  
    case  DIRECTIVE : return DIRECTIVE_ATTENDUE ; 
    case  INSTRUCTION : return INSTRUCTION_ATTENDUE ; 
    case  INTEGER   : return INT_ATTENDU ; 
    case  CHAINE    : return CHAINE_ATTENDUE ; 
    case  VIRGULE   : return VIRGULE_ATTENDUE ; 
    case  MOINS     : return MOINS_ATTENDU ; 
    case  DEUX_POINTS     : return DEUXPOINTS_ATTENDU ; 
    case  PAR_OUV   : return PAROUV_ATTENDUE ; 
    case  PAR_FERM  : return PARFERM_ATTENDUE ;  
    case  ACCOL_FERM  : return ACCOLFERM_ATTENDUE ;  
    case  CROCH_FERM  : return CROCHFERM_ATTENDU ;  
    case  ENDLEX    : return NOERR ; 
    case  ERRLEX    : return NOERR ; 
    
    default :
         printf ("Oups! Internal error in CodeDeLexAttendu\n");
         exit (1) ;
   }
}









/* pre-declaration des fonctions d'analyse */

static int   RecInstruction ()  ;
static int   RecDirective ()  ;
static int   RecProg ()  ;
static int   RecLigne ()  ;
static char *RecParamChaine ()  ;
static char *RecParamEtiq ()  ;
static int   RecParamInst (ParamInst *) ;
static int   RecExp (ParamExp *) ;
static int   RecIndexExp (ParamInst *) ;
static int   RecEtiqImm (ExpImmEtiq *, int) ;
static int   RecShiftExp (ParamInstShift *);
static Lexeme RecLex (NomLexeme) ;
static long  RecParamIntBounded (int) ;
static int   RecParamReserv (int, LigneLog *) ;
static int   RecParamIntAlign ();
/* Analyse 
 * - La fonction principale d'analyse.
 * PARAM fpin : un pointeur de fichier ouvert en lecture
 * PARAM LeProg : adresse d'un tableau de lignes alloue par ailleurs
 * PARAM p_nbLigneLog : resultat, nombre de lignes reconnues ici
 * RESULT : 0 si pas d'erreur, != 0 sinon. 
 *          rend le programe utilisable dans un Makefile ou un shell
 *          car 0 est la convention unix pour ``pas d'erreur''.
 */
int Analyse (FILE *fpin, Elem *LeProg, int *p_nbLigneLog) {


    int result ;

   DemLex (fpin) ;
   result =  RecProg (LeProg, p_nbLigneLog) ;
   if (result == 0 ) printf ("Syntaxe correcte\n") ;

   return result ; 
}
/* RecLex 
 * - Reconnaissance d'un lexème
 * PARAM : n nature de lexeme 
 * RESULT : le lexeme reconnu (si on a besoin des morceaux)
 */
static Lexeme RecLex (NomLexeme n) {
   Lexeme r ; 
   if (LexCour().nat != n)
      ErreurSynt (CodeDeLexAttendu (n), LexCour()) ;
   else {
      r = LexCour() ;
      AvLex () ;
      return r ;
   }
}
/* RecProg
 * - Reconnaissance d'un programme complet 
 * PARAM  : P un programme à remplir 
 * PARAM  : nbl  nb de lignes reconnues (a remplir)
 * RESULT : 0 si pas d'erreur, != 0 sinon
 */
static int RecProg (UnProg P, int *nbl) {
   int nligne = 0 ;

    while ( LexCour().nat != ENDLEX ) {
      while (LexCour().nat == NL) AvLex() ;
      if ( LexCour().nat != ENDLEX ) {
         RecLigne (P, &nligne) ; 
         RecLex (NL) ;
      }
    }
   *nbl = nligne ;
   return 0 ; /* tout va bien */
}
/* RecLigne
 * - Reconnaissance d'une ligne complete (sans le NL final) 
 * PARAM P   : le programme a construire 
 * PARAM nligne : donnee/resultat 
 *             numero de la prochaine ligne a construire
 */
static int RecLigne (UnProg P, int *nligne) {
Lexeme lelex;
   Elem      *e  = &(P[*nligne])  ; 
   LigneLog  *L  = &(e->ligne) ; /* a construire */ 

   switch (LexCour().nat) {
   case ERRLEX :       ErreurSynt (ERR_LEX, LexCour()) ;
   case ENDLEX :       return 0;

   case NL :           break ; /* rec. ligne vide - ne devrait pas arriver */

   case NOM_REG :
   case INTEGER : 
   case CHAINE : 
   case VIRGULE : 
   case POINT_EXCL :
   case DIESE :
   case MOINS : 
   case PLUS :
   case EGAL :
   case PAR_OUV :
   case PAR_FERM : 
   case ACCOL_OUV :
   case ACCOL_FERM : 
   case CROCH_OUV : 
   case CROCH_FERM : 
   case DEUX_POINTS : 
                      ErreurSynt (DEB_LIGNE, LexCour()) ;

   /* Les cas corrects */ 
   case ETIQUETTE :
        /* un peu trop general : accepte plusieurs etiquettes et une
           instruction ou directive, sur la meme ligne...
           Bof, ca a l'air accepte aussi par gcc.
           On laisse comme ca.*/
      e->nl_source = LexCour().nol ;
      L->nat = LL_ETIQ ; 
      lelex = LexCour();
      L->u.nom_etiq = lelex.chaine ;   
      AvLex() ;
      RecLex (DEUX_POINTS);
      (*nligne)++ ;
      RecLigne (P, nligne) ;
      break ;

   case DIRECTIVE : 
      e->nl_source = LexCour().nol ;
      RecDirective (L) ; 
      (*nligne)++ ;
      break ;


   case INSTRUCTION : 
      e->nl_source = LexCour().nol ;
      RecInstruction (L) ;
      (*nligne)++ ;
      break ;

   default :
      printf ("Oups! Internal error in RecLigne\n");
	   exit(1);
   }
}
/* RecDirective
 * - Reconnaissance d'une directive 
 * PARAM : L  adresse de ligne logique a remplir 
 */
static int RecDirective (LigneLog  *L) {
int result = 0;
         Lexeme laDir = LexCour () ;         
         AvLex () ;
         /* lecture des parametres, selon la nature de
            la directive */
         if      (!strcmp (laDir.chaine, ".align")) {
            L->nat = LL_ALIGN ; 
            L->u.align = RecParamIntAlign () ;
         }
         else if (!strcmp (laDir.chaine, ".text")) {
	    L->nat = LL_SECT;
            L->u.sect = Z_TEXT;
         }
         else if (!strcmp (laDir.chaine, ".data")) {
	    L->nat = LL_SECT;
            L->u.sect = Z_DATA;
         }
         else if (!strcmp (laDir.chaine, ".bss")) {
	    L->nat = LL_SECT;
            L->u.sect = Z_BSS;
         }
         else if (!strcmp (laDir.chaine, ".word")) {
            L->nat       = LL_RESERV_INIT ;
            L->u.uri.dir = R_WORD ;
            RecParamReserv (32, L) ;
         }
         else if (!strcmp (laDir.chaine, ".hword")) {
            L->nat = LL_RESERV_INIT ;
            L->u.uri.dir = R_HALF ;
            RecParamReserv (16, L) ;
         }
         else if (!strcmp (laDir.chaine, ".byte")) {
            L->nat = LL_RESERV_INIT ;
            L->u.uri.dir = R_BYTE ;
            RecParamReserv (8, L) ;
         }
         else if (!strcmp (laDir.chaine, ".asciz")) {
            L->nat = LL_RESERV_INIT ;
            L->u.uri.dir = R_ASCIZ ;
            (L->u.uri.p0).nat = PR_CHAINE ;
            (L->u.uri.p0).chaine = RecParamChaine();
         }
         else if (!strcmp (laDir.chaine, ".ascii")) {
            L->nat = LL_RESERV_INIT ;
            L->u.uri.dir = R_ASCII ;
            (L->u.uri.p0).nat = PR_CHAINE ;
            (L->u.uri.p0).chaine = RecParamChaine();
         }
         else if (!strcmp (laDir.chaine, ".skip")) {
            L->nat = LL_RESERV_N_INIT;
            if (LexCour().nat == INTEGER) {
               L->u.urni.dir = R_INT ;
               L->u.urni.nboctets = LexCour().value;
               AvLex();
            }
            else if (LexCour().nat == ETIQUETTE) {
               L->u.urni.dir = R_ETIQ ;
               L->u.urni.etiq = LexCour().chaine;
               AvLex();
            }
            else ErreurSynt (INT_OU_ETIQ_ATTENDU, LexCour());
         }
         else if (!strcmp (laDir.chaine, ".global")) {
            L->nat = LL_EXPORT ;
            L->u.nom_globl = RecParamEtiq () ;
         }
         else if (!strcmp (laDir.chaine, ".set")) {
            L->nat = LL_CTE ;
            L->u.cte.etiq = RecLex(ETIQUETTE).chaine ;
            RecLex(VIRGULE);
            L->u.cte.valcte = RecLex(INTEGER).value;        
         }
			else ErreurSynt (DIRECTIVE_INCONNUE, LexCour());
   return result;
}
/* RecParamChaine
 * - Reconnaissance d'une chaîne de caractères
 * PARAM 
 * RESULT la chaine reconnue (pointeur)
 */
static char *RecParamChaine () {
char * result ;
   result = RecLex (CHAINE).chaine  ; 
   result[strlen(result)-1] = '\0' ;
   return &(result[1]) ;
}
/* RecParamEtiq
 * - Reconnaissance d'une étiquette
 * PARAM 
 * RESULT : le pointeur de chaine du nom de l'etiquette
 */
static char *RecParamEtiq () {
   return RecLex (ETIQUETTE).chaine ; 
}
static int RecParamInt () {
   return RecLex (INTEGER).value ;
}
static int  RecParamReserv (int size, LigneLog *L) {
   switch (LexCour().nat) {
      case ETIQUETTE :
         (L->u.uri.p0).nat = PR_ETIQUETTE ;
         (L->u.uri.p0).nom_etiq = RecLex (ETIQUETTE).chaine ; 
         break ;   
      case INTEGER : 
         (L->u.uri.p0).nat = PR_NOMBRE ;
         (L->u.uri.p0).nb  = RecParamIntBounded (size) ;
         break ;
      case MOINS :
         (L->u.uri.p0).nat = PR_NOMBRE ;
         AvLex();
         (L->u.uri.p0).nb  = -1 * RecParamIntBounded (size) ;
         break;
      default :
         ErreurSynt (INT_OU_ETIQ_ATTENDU, LexCour()) ;
   }
   
      
}
/* RecParamIntBounded 
 * - Reconnaissance d'un entier borné
A FAIRE : justement le test de limite
 * PARAM bound : nb de bits max 
 * RESULT      : la valeur du lexeme reconnu 
 */
static long RecParamIntBounded (int bound) {
   long val ; 
   if (LexCour().nat != INTEGER)
      ErreurSynt (INT_ATTENDU, LexCour());
   else {
      val = LexCour().value ;
      AvLex () ;
      return val ; 
   }
}
static int RecParamIntAlign () {
   Lexeme L = RecLex (INTEGER) ; 
   if  ( (L.value != 1) &&
        (L.value != 2) &&
        (L.value != 4) &&
        (L.value != 8))
      ErreurSynt (INT_ALIGN_ATTENDU, LexCour());
   else {
      return L.value ;
   }
}
/* RecInstruction
 * - Reconnaissnce d'une instruction 
 * PARAM L : adresse d'une ligne a remplir
 * RESULT : non significatif
 */
static int RecInstruction (LigneLog  *L) {
   int i = 0 ; 
   Lexeme Linst = LexCour () ;
   /* Linst.nat = INSTRUCTION, necessairement */

   L->nat = LL_INST ;
   L->u.uinst.mnemo = LexCour().chaine ;
   L->u.uinst.s_i = LexCour().s_i ;
   AvLex () ;
   if (LexCour ().nat == NL)
      ErreurSynt (ZERO_PARAM_INST, LexCour());
   else {
      RecParamInst (&(L->u.uinst.p[0])) ;
      i = 1;
      if (LexCour ().nat != NL) {
         RecLex (VIRGULE) ;
         RecParamInst (&(L->u.uinst.p[1])) ;
         i++;
      }
      if (LexCour ().nat != NL) {
         RecLex (VIRGULE) ;
         RecParamInst (&(L->u.uinst.p[2])) ;
         i++;
      }
      if (LexCour ().nat != NL) {
         RecLex (VIRGULE) ;
         RecParamInst (&(L->u.uinst.p[3])) ;
         i++;
      }
     L->u.uinst.nbp = i ;
     if (i > 4) 
         ErreurSynt (TROP_PARAM_INST, LexCour());
   }
}
/* RecParamInst
 * - Reconnaissance d'un parametre d'instruction 
 * PARAM : pa adresse de parametre a remplir
 * RESULT : non significatif
*/ 
static int RecParamInst (ParamInst *pa) {
   Lexeme lelexeme ;

   switch (LexCour().nat) {
   case DIESE :
      pa->nat = P_EXP;
      AvLex();
      RecExp (&pa->u.exp);
      break;

   case ETIQUETTE :
      pa->nat = P_EXP ;
      pa->u.exp.nat = P_ETIQUETTE;
      pa->u.exp.nom_etiq = LexCour().chaine ; 
      AvLex () ;
      break ;

   case NOM_REG :
      pa->nat = P_NOMREG ;
      pa->u.noreg = LexCour().noreg ;
      AvLex () ;
      if (LexCour().nat == POINT_EXCL) {
         pa->nat = P_NOMREG_EXCL;
         AvLex();
      }
      break ;
      
   case DIRECTIVE :   /* cas OpShift */
      pa->nat = P_SHIFT;
      RecShiftExp (&pa->u.exp_shift);
      break;

   case CROCH_OUV :
      pa->nat = P_INDIR ;
      AvLex () ;
      lelexeme = RecLex (NOM_REG) ;
      pa->u.indir.nbelt = 1 ;
      pa->u.indir.noreg1 = lelexeme.noreg ;
      if (LexCour().nat == VIRGULE)  {
         /* cas [reg1, #+/-offset] ou [reg1, +/-reg2] ou [reg1, +/-reg2 opshift #imm] */
         /* on a reconnu [reg1 ,  */
         AvLex () ;
         pa->u.indir.nbelt = 2 ;
			RecIndexExp (pa);
      };
      RecLex (CROCH_FERM) ;
      break ;

   case ACCOL_OUV :
      pa->nat = P_REGS;
      AvLex () ;
      lelexeme = RecLex (NOM_REG) ;
      pa->u.regs[lelexeme.noreg] = 1;
      while (LexCour().nat == VIRGULE) {
        AvLex();
        lelexeme = RecLex (NOM_REG) ;
        pa->u.regs[lelexeme.noreg] = 1;
      }
      RecLex (ACCOL_FERM) ;
      break ;
   default :
	  ErreurSynt (DEB_PARAM_INST, LexCour());
   }
}
/* RecExp
 * - Reconnaissance d'un paramètre d'instruction de type expression : 
     valeur immédiate ou liste d'expressions separées par des moins
 * PARAM : pe adresse de parametre a remplir
 * RESULT : non significatif
*/ 
static int RecExp (ParamExp *pe) {
int nbe, val;
Lexeme lelex;
struct pe *ptexp;
struct pe *ptprec;

   lelex = LexCour();
   switch (lelex.nat) {
   case INTEGER :
     pe->nat = P_IMMEDIAT;
     val = RecLex(INTEGER).value ;
     pe->valimm = val ;
     pe->tabexp[0].valimm = val ; /* sparadrap */
     break;
   case ETIQUETTE :
     pe->nat = P_ETIQUETTE;
     pe->nom_etiq = LexCour().chaine ;
     break;
   case PLUS:
   case MOINS:
     if (lelex.nat==PLUS) pe->signe = S_PLUS; else pe->signe = S_MOINS;
     AvLex();
     if (LexCour().nat == INTEGER) {
         pe->nat = P_IMMEDIAT;
	 val = RecLex(INTEGER).value ;
         if (lelex.nat == PLUS) {
		pe->valimm = val ; 
		pe->tabexp[0].valimm = val ;
	 } else {
		pe->valimm = -1 * val ;
		pe->tabexp[0].valimm = -1 * val ;
	} ;
     }
     else if (LexCour().nat == ETIQUETTE) {
         pe->nat = P_ETIQUETTE;
         pe->nom_etiq = LexCour().chaine;
     }
     else ErreurSynt (INT_OU_ETIQ_ATTENDU ,LexCour());
     break;
   case  PAR_OUV :
     pe->nat = P_EXP;
     AvLex();
     nbe = 0;
     RecEtiqImm (pe->tabexp, nbe);
     nbe++;
     pe->nbexp = nbe;
     while (LexCour().nat == MOINS) {
        AvLex();
        if (nbe <= NBE_EXPSTAT) {
           RecEtiqImm (pe->tabexp, nbe);
           nbe++;
           pe->nbexp = nbe;
        }
        else ErreurSynt (TROP_EXP, LexCour());
     }
     RecLex(PAR_FERM);
     break;
   default :
	  ErreurSynt (DEB_EXPRESSION, LexCour());
   }
}
/* RecIndexExp
 * - Reconnaissance d'une partie d'un paramètre d'instruction
     de type expression index : 
	  on a reconnu precedemment reconnu [reg1 , 
 * PARAM : pa adresse du parametre d'instruction a remplir
 * RESULT : non significatif
*/ 
static int RecIndexExp (ParamInst *pa) {
   if (LexCour().nat==DIESE) {
      pa->u.indir.nat = IND_EXP;
      AvLex();
      RecExp ( & pa->u.indir.exp);
   }
   else if ( (LexCour().nat==NOM_REG) ||
             (LexCour().nat==PLUS) || (LexCour().nat==MOINS) )  {
           switch (LexCour().nat) {
           case PLUS :
           case MOINS :
              if (LexCour().nat==PLUS) pa->u.indir.signe = S_PLUS; 
              if (LexCour().nat==MOINS) pa->u.indir.signe = S_MOINS;
              AvLex () ;
              if (LexCour().nat==NOM_REG) {
                 pa->u.indir.nat = IND_NOMREG;
                 pa->u.indir.noreg2 = LexCour().noreg ;
                 AvLex() ;
              } else ErreurSynt (NOM_REG_ATTENDU , LexCour());
              break ;
           case NOM_REG :
              pa->u.indir.nat = IND_NOMREG;
              pa->u.indir.signe = S_PLUS;
              pa->u.indir.noreg2 = LexCour().noreg ;
              AvLex() ;
              break ;
           default :
                printf ("Oups! Internal error in RecIndexExp\n");
                exit (1) ;
           }
           /* reste a traiter expression shift eventuelle */
           if (LexCour().nat==VIRGULE) {
             AvLex() ;
             pa->u.indir.nat = IND_NOMREG_SHIFT;
             RecShiftExp (&pa->u.indir.exp_shift);
           }
   }
   else ErreurSynt (DIESE_PLUS_MOINS_REG, LexCour());
}
/* RecShiftExp
 * - reconnaissance d'une expression shift le registre precedent a ete reconnu
 * PARAM : ps adresse de parametre shift a remplir
 * RESULT : non significatif
*/

static int RecShiftExp (ParamInstShift *ps) {
Lexeme ladir ;
    ladir = LexCour();
    if ((ladir.nat == DIRECTIVE) &&
        (  (!strcmp (ladir.chaine, "LSL")) || (!strcmp (ladir.chaine, "LSR")) ||
           (!strcmp (ladir.chaine, "ASR")) || (!strcmp (ladir.chaine, "ROR")) ) ) {
       ps->dir_shift = ladir.chaine;
       AvLex();
       if (LexCour().nat == DIESE) {
          AvLex();
          ps->nat = P_IMMEDIAT ;
          ps->valimmshift = RecLex(INTEGER).value;
       }
       else {
          ps->noregshift = RecLex(NOM_REG).noreg;
          ps->nat = P_NOMREG ;
       }
    }
    else if ((ladir.nat == DIRECTIVE) && (!strcmp (ladir.chaine, "RRX"))) {
       ps->dir_shift = ladir.chaine;
       AvLex();
    }
    else ErreurSynt (DIR_SHIFT_ATTENDUE , LexCour());
}
/* RecEtiqImm
 * - Reconnaissance d'une expression d'une liste d'exp (e1-e2-...)
     ce sont soit des étiquettes, soit des valeurs immédiates
 * PARAM : exp adresse de parametre a remplir
           no numero de l'expression dans le tableau d'expressions
 * RESULT : non significatif
*/
static int RecEtiqImm (ExpImmEtiq tabexp[], int no) {
   switch (LexCour().nat) {
   case INTEGER :
     tabexp[no].nat = P_IMMEDIAT;
     tabexp[no].valimm = LexCour().value;
     break;
   case ETIQUETTE :
     tabexp[no].nat = P_ETIQUETTE;
     tabexp[no].nom_etiq = LexCour().chaine;
     break;
   default :
     ErreurSynt (INT_OU_ETIQ_ATTENDU, LexCour());
   }
   AvLex();
}
/* pre-declarations - voir ci-dessous */
static int VerifInst (Elem) ;
static int VerifReservInit(Elem) ;


/* ---------------------------------------------------------------
 * Verif
 * - Verification de contraintes supplementaires sur les pg
 *   qui ont deja passe la phase d'analyse syntaxique HC pure.
 *   On travaille maintenant sur une structure de donnees interne
 *    fabriquee au cours de l'analyse (definie par AA.h) :
 * RESULT           : nombre d'erreurs.
 * ---------------------------------------------------------------
 */
int Verif (Elem *LeProg, int nbLigneLog) {
int i ;
int result = 0 ;

   for (i = 0 ; i < nbLigneLog ; i++) {
      Elem     E = LeProg[i] ;
      LigneLog L = E.ligne ;

      switch (L.nat) {
         case LL_NONE          :
            break ;
         case LL_ETIQ         :
            /* rien a verifier, localement */
            break ;
         case LL_INST :
            /* C'est le cas le plus complique. Verif des
             * modes d'adressage autorises
             */
            result += VerifInst (E) ;
            break ;
         case LL_EXPORT         :
            /* rien a verifier, localement */
            break  ;
         case LL_SECT          :
            /* rien a verifier, localement */
            break   ;
         case LL_RESERV_N_INIT        :
            /* reservations non init. Verifier que la taille
                   demandee est positive !
                */
            /* ... */
            break  ;
         case LL_RESERV_INIT   :
            /* verifier la taille de la donnee par rapport
                 * a la taille de la zone reservee.
              */
            result += VerifReservInit (E) ;
            break ;
         case LL_ALIGN         :
            /* rien a verifier, localement, sauf que l'entier
               qui donne la borne d'alignement est positif.  */
                           /* l'entier doit etre 1,2,4,8, deja fait lors
                                   de l'analyse syntaxique */
            /* ... */
            break  ;
      }
   }
   return result ;
}

/* ---------------------------------------------------------------
 * VerifInst
 * - Verification d'une instruction.
 * PARAM : un element de tableau contenant une
 *         ligne logique (garantie d'instruction)
 * RESULT : 0 si ok.
 * ---------------------------------------------------------------
 */
static int VerifInst (Elem E) {
int i ;
int result = 0;
LigneLog L = E.ligne ;
char *mnemo = L.u.uinst.mnemo ;

   /* Verification du nombre de parametres, des modes d'adressages autorises.
     * ----------------------------------------------
   */

        /* A FAIRE */

  return result;
}
/* ---------------------------------------------------------------
 * Verif
 * - Verification d'une réservation initialisée (pb de taille)
 * PARAM : un element de tableau contenant une
 *         ligne logique (garantie de réservation initialisée)
 * RESULT : 0 si ok.
 * ---------------------------------------------------------------
 */
static int VerifReservInit (Elem E) {
int result = 0;
LigneLog L = E.ligne ;

   /* A FAIRE */

   return result ;
}
static taillesDeSections lesTaillesDeSections ;
/* predeclarations */
static void     CalculAdrEtZones  () ;
static void     GenereTSetTC () ;

/* ---------------------------------------------------------------
 * Decoration
 * --------------------------------------------------------------- 
 */
void  Decoration (Elem *LeProg, int nbLigneLog) {
   
   CalculAdrEtZones (LeProg, nbLigneLog) ;
   GenereTSetTC (LeProg, nbLigneLog) ;

}
/* ---------------------------------------------------------------------
 * CalculAdrEtZones
 * - Parcours des lignes logiques pour calculer les adresses
 * et les tailles des zones TEXT et DATA 
 * Stockage dans les champs additionnels de la structure Elem.
 * ---------------------------------------------------------------------
 */
static void     CalculAdrEtZones  (Elem *LeProg, int nbLigneLog) {
int i ;
int cpt_zone[4]={0, 0, 0, 0} ; 	/* tableau de compteur indice par NomZone */
					/* Z_TEXT, Z_DATA, Z_BSS, Z_NONE */
int nb_elem[4]={0, 0, 0, 0} ; 	/* tableau de nbre d'elem indice par NomZone */
					/* Z_TEXT, Z_DATA, Z_BSS, Z_NONE */
int nb_elem_txt=0, nb_data=0 ;	/* nbre d'elements en zone TEXT et DATA */
NomZone zone_cour = Z_TEXT ;		/* initialement on est en Z_TEXT */
int lg_chaine ;


   for (i = 0 ; i < nbLigneLog ; i++) {
      Elem     *pE = &(LeProg[i]) ;
      LigneLog L = pE->ligne ;

      pE->zone_cour = zone_cour ;		/* zone courante */
      pE->ad_dans_zone = cpt_zone[zone_cour] ;  /* adresse dans la zone courante */

      switch (L.nat) {
         case LL_NONE          :
            break ;
         case LL_ETIQ         :
            break ;
         case LL_INST :
		pE->nb_bits = 32 ;	/* instructions toujours sur 4 octets */
		cpt_zone[zone_cour] +=4 ;
		nb_elem[zone_cour] +=1;
            break ;
         case LL_EXPORT         :
            break  ;
         case LL_SECT          :
		zone_cour = L.u.sect ;
            break   ;
         case LL_RESERV_N_INIT        :
		pE->nb_bits = L.u.urni.nboctets*4 ;
		cpt_zone[zone_cour] += L.u.urni.nboctets ;
		nb_elem[zone_cour] +=1;
            break  ;
         case LL_RESERV_INIT   :	/* A VERIFIER !!! */	
		nb_elem[zone_cour] +=1;
		switch (L.u.uri.dir) {		
		  case R_WORD:	/* tjrs 4 octets */
			pE->nb_bits = 32 ;
			cpt_zone[zone_cour] +=4 ;
		      break ;
		  case R_HALF:	/* tjrs 2 octets */
			pE->nb_bits = 16 ;
			cpt_zone[zone_cour] +=2 ;
		      break ;
		  case R_BYTE: /* tjrs 1 octet */	
			pE->nb_bits = 8 ;
			cpt_zone[zone_cour] +=1 ;
		      break ;
		  case R_ASCIZ:
			lg_chaine = strlen(L.u.uri.p0.chaine) ;
			pE->nb_bits = (lg_chaine+1)*8 ;
			cpt_zone[zone_cour] += lg_chaine+1 ;
			break ;
		};
		
            break ;
         case LL_ALIGN         : /* A VERIFIER !!! */
		nb_elem[zone_cour] +=1;
		pE->nb_bits = 8* 
			(cpt_zone[zone_cour] % L.u.align ?
				L.u.align - (cpt_zone[zone_cour] % L.u.align)
						:
				0
			) ;
		cpt_zone[zone_cour] += (pE->nb_bits)/8 ;
            break  ;
      }
   }

   lesTaillesDeSections.theTextZone_nelem = nb_elem[Z_TEXT] ;
   lesTaillesDeSections.theDataZone_nelem = nb_elem[Z_DATA] ;
}

#define CHARTABLESIZE 5000
static char TheCharTable[CHARTABLESIZE] ;
static Asymbol TheSymbolTable[MAXSYMBOLS] ;
static void InsererDansTS(int indice, NomZone zone, unsigned long value, 
	unsigned long adr_TC, LocGlob portee) {
	TheSymbolTable[indice].Zone = zone ;
	TheSymbolTable[indice].Value = value ;
	TheSymbolTable[indice].AdressInCharTable = adr_TC ;
	TheSymbolTable[indice].portee = portee ;
}
static int ChercherDansTS(char *chaine, int nb_symb ) {
int i ;
   for (i=0 ; i < nb_symb ; i++) {
    if (!strcmp(chaine, &(TheCharTable[TheSymbolTable[i].AdressInCharTable])))
	return i ;
   }
   return -1 ;	
}
static void InsererDansTC(int indice, char *chaine) {
	strcpy(&(TheCharTable[indice]), chaine) ;
}
void DumpTS() {
int i ;
char *nom_symb ;
NomZone zone ;
unsigned long value ;
LocGlob portee ;
unsigned long adr_TC ;

	printf("ZONE | val  | P | @TC| nom\n") ;
	for (i=0 ; i< lesTaillesDeSections.theSymbolTable_nelem ; i++) {
	  zone = TheSymbolTable[i].Zone ;
          value = TheSymbolTable[i].Value ;
          adr_TC = TheSymbolTable[i].AdressInCharTable ;
          portee = TheSymbolTable[i].portee ;
	  nom_symb = &(TheCharTable[adr_TC]) ;
	  printf("%s | %4d | %d | %2d | %s \n", 
		NomZone2String(zone), value, portee, adr_TC, nom_symb) ;

	}

}

/* ---------------------------------------------------------------------
 * CalculTSetTC
 * - Parcours des lignes logiques pour construire la Table des Symboles
 *  et la Table des Chaines intermediaires
 * ---------------------------------------------------------------------
 */
static void     GenereTSetTC(Elem *LeProg, int nbLigneLog) {
int i ;
int nb_symb = 0 ;
unsigned long nb_char = 0 ;
char *nom_symb ;
NomZone zone ;
unsigned long value ; 
LocGlob portee ;
int ind_ds_TS ;
ParamInst p ;
ParamReserv pr ;


 for (i = 0 ; i < nbLigneLog ; i++) {
      Elem     *pE = &(LeProg[i]) ;
      LigneLog L = pE->ligne ;
      switch (L.nat) {
         case LL_NONE          :
            break ;
         case LL_ETIQ         :
		nom_symb = L.u.nom_etiq ;
		ind_ds_TS = ChercherDansTS(nom_symb, nb_symb) ;
		if (ind_ds_TS == -1) { 	/* symbole absent */
			zone = pE->zone_cour ;
			value = pE->ad_dans_zone ;
			portee = Local ;
			InsererDansTC(nb_char, nom_symb) ;
			InsererDansTS(nb_symb, zone, value, nb_char, portee) ;
			nb_char+=strlen(nom_symb) +1 ;
			nb_symb++ ;
		  }
		else  { /* symbole present */
			if (TheSymbolTable[ind_ds_TS].Zone == Z_NONE) {
				/* c'est la 1ere def */
 				 zone = pE->zone_cour ;
				 value = pE->ad_dans_zone ;
				 TheSymbolTable[ind_ds_TS].Value = value ;
				 TheSymbolTable[ind_ds_TS].Zone = zone ;
			}
			else printf("ON RALE  : double def") ;
		  }
            break ;
         case LL_INST :
			/* on pourrait remplacer par une iteration ! */
		switch (L.u.uinst.nbp) {
		   case 4 :
			p = L.u.uinst.p[3] ;
			if ((p.nat == P_EXP) && (p.u.exp.nat == P_ETIQUETTE)) {
			  nom_symb = p.u.exp.nom_etiq ;
			  ind_ds_TS = ChercherDansTS(nom_symb, nb_symb) ;
			  if (ind_ds_TS == -1) {  /* symbole absent */
			    InsererDansTC(nb_char, nom_symb) ;
                            InsererDansTS(nb_symb, Z_NONE, 0, nb_char, Local) ;
                            nb_char+=strlen(nom_symb) +1 ;
                            nb_symb++ ;
					}
				}
		   case 3 :
			p = L.u.uinst.p[2] ;
			if ((p.nat == P_EXP) && (p.u.exp.nat == P_ETIQUETTE)) {
			  nom_symb = p.u.exp.nom_etiq ;
			  ind_ds_TS = ChercherDansTS(nom_symb, nb_symb) ;
			  if (ind_ds_TS == -1) {  /* symbole absent */
			    InsererDansTC(nb_char, nom_symb) ;
                            InsererDansTS(nb_symb, Z_NONE, 0, nb_char, Local) ;
                            nb_char+=strlen(nom_symb) +1 ;
                            nb_symb++ ;
					}
				}
		   case 2 :
			p = L.u.uinst.p[1] ;
			if ((p.nat == P_EXP) && (p.u.exp.nat == P_ETIQUETTE)) {
			  nom_symb = p.u.exp.nom_etiq ;
			  ind_ds_TS = ChercherDansTS(nom_symb, nb_symb) ;
			  if (ind_ds_TS == -1) {  /* symbole absent */
			    InsererDansTC(nb_char, nom_symb) ;
                            InsererDansTS(nb_symb, Z_NONE, 0, nb_char, Local) ;
                            nb_char+=strlen(nom_symb) +1 ;
                            nb_symb++ ;
					}
				}
		   case 1 :
			p = L.u.uinst.p[0] ;
			if ((p.nat == P_EXP) && (p.u.exp.nat == P_ETIQUETTE)) {
			  nom_symb = p.u.exp.nom_etiq ;
			  ind_ds_TS = ChercherDansTS(nom_symb, nb_symb) ;
			  if (ind_ds_TS == -1) {  /* symbole absent */
			    InsererDansTC(nb_char, nom_symb) ;
                            InsererDansTS(nb_symb, Z_NONE, 0, nb_char, Local) ;
                            nb_char+=strlen(nom_symb) +1 ;
                            nb_symb++ ;
					}
				}
			break ;
		   default : break ;   
		}
            break ;
         case LL_EXPORT         :
		nom_symb = L.u.nom_globl ;
		ind_ds_TS = ChercherDansTS(nom_symb, nb_symb) ;
		if (ind_ds_TS == -1) {  /* symbole absent */
			 InsererDansTC(nb_char, nom_symb) ;
                         InsererDansTS(nb_symb, Z_NONE, 0, nb_char, Global) ;
                         nb_char+=strlen(nom_symb) +1 ;
                         nb_symb++ ;
			}
		else {
			TheSymbolTable[ind_ds_TS].portee = Global ;
		}
            break  ;
         case LL_SECT          :
            break   ;
         case LL_RESERV_N_INIT        :
            break  ;
         case LL_RESERV_INIT   :       
		pr = L.u.uri.p0 ;
                if (pr.nat == PR_ETIQUETTE) {
                   nom_symb = pr.nom_etiq ;
                   ind_ds_TS = ChercherDansTS(nom_symb, nb_symb) ;
                   if (ind_ds_TS == -1) {  /* symbole absent */
                            InsererDansTC(nb_char, nom_symb) ;
                            InsererDansTS(nb_symb, Z_NONE, 0, nb_char, Local) ;
                            nb_char+=strlen(nom_symb) +1 ;
                            nb_symb++ ;
                                        }
                                }
            break ;
         case LL_ALIGN : 
            break  ;
      }
 }

 /* Il reste a parcourir la TS pour transformer les 
	symboles (Z_NONE, Local) en (Z_NONE, Global) */

 for (i=0 ; i<nb_symb ; i++) {
	if (TheSymbolTable[i].Zone == Z_NONE && 
			TheSymbolTable[i].portee == Local)	
		TheSymbolTable[i].portee = Global ;
 } 
 
 lesTaillesDeSections.theCharTable_size = nb_char ;
 lesTaillesDeSections.theSymbolTable_nelem = nb_symb ;
 }

static void EcrireTC(FILE *f) {

  int i ;

  fprintf (f, "%d,%d\n", lesTaillesDeSections.theCharTable_size,
				lesTaillesDeSections.theSymbolTable_nelem) ;
  for (i=0 ; i<lesTaillesDeSections.theCharTable_size ; i++)
	if (TheCharTable[i] != '\0') 
		fprintf (f, "%c", TheCharTable[i]) ;   
	else
		fprintf (f, "\n") ;   

}


static char *NomPortee2String (LocGlob portee) {
  switch (portee) {
	case Local : return ("N_EXT") ;
	case Global : return ("EXT") ;
  } 
} 

static void EcrireTS(FILE *f) {
int i ;
char *nom_symb ;
NomZone zone ;
unsigned long value ;
LocGlob portee ;
unsigned long adr_TC ;

  fprintf (f, "%d\n", lesTaillesDeSections.theSymbolTable_nelem) ;
  for (i=0 ; i< lesTaillesDeSections.theSymbolTable_nelem ; i++) {
          adr_TC = TheSymbolTable[i].AdressInCharTable ;
          value = TheSymbolTable[i].Value ;
          zone = TheSymbolTable[i].Zone ;
          portee = TheSymbolTable[i].portee ;
          fprintf(f, "%d \t %d \t %d \t %s \t %s \n",
            i, adr_TC, value, NomZone2String(zone), NomPortee2String(portee)) ;
  }
}

static int CalculExp(ParamExp exp) {
int num_symb, nb_symb=lesTaillesDeSections.theSymbolTable_nelem ;
int i, result ;

  if (exp.tabexp[0].nat == P_IMMEDIAT) {
	result = exp.tabexp[0].valimm ;
  } else {
	num_symb = ChercherDansTS(exp.tabexp[0].nom_etiq, nb_symb) ;
	result = TheSymbolTable[num_symb].Value ;
  } ;
  for (i=1 ; i<exp.nbexp ; i++) {
    if (exp.tabexp[i].nat == P_IMMEDIAT) 
	result -= exp.tabexp[i].valimm ;
    else {
	num_symb = ChercherDansTS(exp.tabexp[i].nom_etiq, nb_symb) ;
	result -= TheSymbolTable[num_symb].Value ;
    } ;
  } ;
  return (result) ;
}

/* Hyp : le parametre eventuel de type P_SHIFT est toujours le dernier */

static void  EcrireParam(FILE *f, LigneLog L) {
int num_symb, nb_symb=lesTaillesDeSections.theSymbolTable_nelem ;
int i, ip, nb_param, val ;
int p_shift_present = 0 ;
ParamInst p ;
ParamInstShift param_shift ;

/* on fait un 1er parcours pour savoir s'il y a du P_SHIFT */

  for (ip=0 ; ip<L.u.uinst.nbp ; ip++) 
	p_shift_present |= (L.u.uinst.p[ip].nat == P_SHIFT) ;

 /* on ecrit le nombre de parametres */

  nb_param = (p_shift_present ? L.u.uinst.nbp-1 : L.u.uinst.nbp) ;
  fprintf(f, " %d ", nb_param) ;

 /* on ecrit chaque parametre au format .alf */

  for (ip=0 ; ip<nb_param ; ip++) {
  p = L.u.uinst.p[ip] ;
  fprintf(f, "(") ;
  switch (p.nat) {
    case P_EXP:
	switch(p.u.exp.nat) {
	  case P_IMMEDIAT:
		fprintf(f, "IMM %d", p.u.exp.valimm) ;
		break ;
	  case P_ETIQUETTE:
		num_symb = ChercherDansTS(p.u.exp.nom_etiq, nb_symb) ;
		fprintf(f, "SYMB %d", num_symb) ;
		break ;
	} ;
	break ;
    case P_NOMREG:
	if (ip==L.u.uinst.nbp-1 || L.u.uinst.p[ip+1].nat != P_SHIFT)
	   /* parametre courant non suivi par un P_SHIFT */
	   fprintf(f, "REG_S %d", p.u.noreg) ;
	else {
	  /* parametre courant non suivi un P_SHIFT */
       	   param_shift = L.u.uinst.p[ip+1].u.exp_shift ;		
	   if (param_shift.nat == P_IMMEDIAT) 
		fprintf(f, "REG_DEC_I %d %s %d", 
			p.u.noreg, param_shift.dir_shift, 
						param_shift.valimmshift) ;
	   else 
		fprintf(f, "REG_DEC_R %d %s %d", 
			p.u.noreg, param_shift.dir_shift, 
						param_shift.noregshift) ;
	} ;
	break ;
    case P_NOMREG_EXCL:
	fprintf(f, "REG_MAJ %d", p.u.noreg) ;
	break ;
    case P_REGS:
	fprintf(f, "LISTE_REG ") ;
	for (i=0; i<16; i++) fprintf (f, "%1d", p.u.regs[i]) ;
	break ;
    case P_INDIR:
	if (p.u.indir.nbelt == 1) {
	  fprintf (f, "INDIR_I %d + 0", p.u.indir.noreg1) ;
	} else {
  	  switch(p.u.indir.nat) {
		case IND_EXP:
		  val = CalculExp(p.u.indir.exp) ; /* CHANGMT */
		  fprintf(f, "INDIR_I %d %c %d",
			p.u.indir.noreg1,
			((val<0)? '-' : '+'),
			((val<0)? -1*val: val)) ;
		  break ;
		case IND_NOMREG:
		  fprintf(f, "INDIR_R %d %c %d",
			p.u.indir.noreg1,
			(p.u.indir.signe==S_MOINS ? '-' : '+'),
			p.u.indir.noreg2) ;
		  break ;
		case IND_NOMREG_SHIFT:
		  fprintf(f, "INDIR_DEC_I %d %c %d %s %d",
			p.u.indir.noreg1,
			(p.u.indir.signe==S_MOINS ? '-' : '+'),
			p.u.indir.noreg2,
			p.u.indir.exp_shift.dir_shift,
			p.u.indir.exp_shift.valimmshift) ;
		  break ;
	  } ;
	} ;
	break ;
    case P_SHIFT:	
		/* ne devrait pas se produire ... */
	break ;
    default:
	printf("Parametre non traite dans l'ecriture de la zone Text\n");
  } ;
  fprintf(f, ")\t") ;
  } ;
}

static void EcrireTextOuData(FILE *f, NomZone zcour) {
int i ;
ParamReserv p;
int num_symb, nb_symb=lesTaillesDeSections.theSymbolTable_nelem ;
champs_inst s_i ;

  if (zcour == Z_DATA) 
  	fprintf (f, "%d\n", lesTaillesDeSections.theDataZone_nelem) ;
  else
  	fprintf (f, "%d\n", lesTaillesDeSections.theTextZone_nelem) ;

  for (i = 0 ; i < nbLigneLog ; i++) {
      Elem     *pE = &(LeProg[i]) ;
      LigneLog L = pE->ligne ;
      if (pE->zone_cour == zcour) {
      switch (L.nat) {
         case LL_INST:
		/* le mnemonique decode */
		s_i = L.u.uinst.s_i ;
		fprintf(f, "(%s %s %1d %c %1d %s)\t", 
			s_i.base, s_i.cond, s_i.cod_cond,
                       s_i.BHW, s_i.S,
			(s_i.pile[0]!='\0' ? s_i.pile : "XX")) ;
		EcrireParam(f, L) ; /* les parametres ... */
		fprintf(f, "\n") ;
	 	break ;
         case LL_RESERV_N_INIT:
		if (L.u.urni.dir == R_INT) {	/* skip */	
		  fprintf(f, "SKIP %d \n", L.u.urni.nboctets) ;
		} ;
		break ;
         case LL_ALIGN:
		  /* on ne genere rien si l'alignement est deja correct */
		  if (pE->nb_bits != 0) 
		  	fprintf(f, "SKIP %d \n", pE->nb_bits/8) ;
		break ;
         case LL_RESERV_INIT:
		p= L.u.uri.p0 ; 
		switch (L.u.uri.dir) {
		  case R_WORD:
			fprintf(f, "WORD ") ;
			if (p.nat == PR_NOMBRE) 
			  fprintf(f, "DATA_IMM %d\n", p.nb) ;
			else {
			  num_symb = ChercherDansTS(p.nom_etiq, nb_symb) ;
			  fprintf(f, "DATA_SYMB %d\n", num_symb) ;
			} ;
			break;
		  case R_HALF:
			fprintf(f, "HALF ") ;
			if (p.nat == PR_NOMBRE) 
			  fprintf(f, "DATA_IMM %d\n", p.nb) ;
			else {
			  num_symb = ChercherDansTS(p.nom_etiq, nb_symb) ;
			  fprintf(f, "DATA_SYMB %d\n", num_symb) ;
			} ;
			break;
		  case R_BYTE:
			fprintf(f, "BYTE ") ;
			if (p.nat == PR_NOMBRE) 
			  fprintf(f, "DATA_IMM %d\n", p.nb) ;
			else {
			  num_symb = ChercherDansTS(p.nom_etiq, nb_symb) ;
			  fprintf(f, "DATA_SYMB %d\n", num_symb) ;
			} ;
			break;
		  case R_ASCIZ:
			fprintf(f, "ASCIZ \"%s\"\n", p.chaine) ;
			break;
		  default:
			printf("cas non traite en ecriture de la zone Data\n") ;
		} ;
		break ;
	default:
		break ;
  	} ;
        } ;
  } ;
}


void Phase1(FILE *fsource, FILE *finterm) ;


/*
#define MAX_LIGNE_LOG 1000
static Elem LeProg[MAX_LIGNE_LOG] ;
static int nbLigneLog ;
*/
void Phase1(FILE *fsource, FILE *finterm) {
int result_phase_1 = 0 ;


   result_phase_1 = Analyse (fsource, LeProg, &nbLigneLog) ;
   if (result_phase_1 != 0) {
        printf("Erreur de syntaxe - arret \n") ;
        exit(2);
   }

/* Phase de verifications supplementaires
 * verifs contextuelles (forme des instructions, doubles defs de symboles...)
 */

   result_phase_1  = Verif (LeProg, nbLigneLog) ;
   if (result_phase_1 != 0) {
        printf("Erreur de syntaxe contextuelle - arret \n") ;
        exit(3);
   }

/* Enrichissement de la structure de donnees
 * calcul des valeurs et des zones de def des symboles,
 * generation de la table des symboles et de la table des chaînes
 */

   Decoration (LeProg, nbLigneLog) ;

/* Affichage apres deco */

/*
   DumpSdd(LeProg, nbLigneLog) ;
        printf("\n\n\n") ;
   DumpTS() ;
*/

/* Ecriture du resultat dans le fichier .alf */

   EcrireTC(finterm) ;
   EcrireTS(finterm) ;
   EcrireTextOuData(finterm, Z_TEXT) ;
   EcrireTextOuData(finterm, Z_DATA) ;
   fclose(finterm) ;
}
