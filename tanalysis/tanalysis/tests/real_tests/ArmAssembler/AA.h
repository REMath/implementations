#include "MachineLex.h"

/* ----------------------- AA .h -----------------------------
 * 
 *  Structure de donnees pour le stockage des informations
 *  d'un programme en assembleur ARM correct.
 *  
 * -----------------------------------------------------------
 */


typedef enum { Z_TEXT, Z_DATA, Z_BSS,  Z_NONE  } NomZone ;
typedef enum { R_WORD, R_HALF, R_BYTE, R_ASCIZ, R_ASCII, R_INT, R_ETIQ } DirReserv ;


typedef enum { 
   LL_NONE, LL_ETIQ, LL_CTE,  LL_INST,   LL_SECT, LL_EXPORT,
   LL_RESERV_N_INIT, LL_RESERV_INIT, LL_ALIGN
} NatLigneLog ; 


typedef enum {
   P_IMMEDIAT, P_EXP, P_NOMREG, P_NOMREG_EXCL, P_ETIQUETTE, P_SHIFT,
   P_INDIR, P_REGS
} NatParamInst ;

typedef enum {
   IND_IMM, IND_EXP_ETIQ, IND_EXP,
   IND_NOMREG, IND_NOMREG_SHIFT,
} NatParamIndir ;

typedef enum {
   S_PLUS, S_MOINS
} SigneParam;

typedef enum {
   PR_CHAINE, PR_NOMBRE, PR_ETIQUETTE
} NatParamReserv ;

/* parametre de la forme (e1 - e2 - e3...)
   ei est soit une etiquette, soit un entier
   represente par un tableau de NBE_EXPSTAT expressions au max */

#define NBE_EXPSTAT 5

typedef struct {
   NatParamInst nat; /* P_IMMEDIAT ou P_ETIQUETTE */
   char *nom_etiq;
   long valimm;
} ExpImmEtiq;

typedef struct {
   NatParamInst nat ; /* P_IMMEDIAT, P_ETIQUETTE ou P_EXP */
   long valimm ; /* cas P_IMMEDIAT */
   char *nom_etiq ; /* cas P_ETIQUETTE, il peut y avoir un signe */
   SigneParam signe ;
   int nbexp;   /* cas P_EXP */
   ExpImmEtiq tabexp [NBE_EXPSTAT];
} ParamExp;

typedef struct {
      char  *dir_shift ; /* LSL, LSR, ASR, ROR ou RRX */
      NatParamInst nat ; /* P_NOMREG ou P_IMMEDIAT */
      long valimmshift ;
      int noregshift ;
} ParamInstShift ;

/* opérande d'instruction */

typedef struct {
   NatParamInst nat ;
   union {
      /* cas expression : P_EXP */
      ParamExp exp ;

      /* cas nom de registre : P_NOM_REG  ou P_NOM_REG_EXCL */
      int noreg ;

      /* cas p_indir : P_INDIR */
      /* il y a un ou deux elements (nbelt),
         le premier est un registre : noreg1
         le deuxieme eventuel est un registre complete d'un shift eventuel,
         un nombre ou une liste d'expressions */
      struct {
          int nbelt ;
          int noreg1 ;

          NatParamIndir nat ;
             /* nature du deuxième paramètre :
                IND_EXP, IND_NOMREG, IND_NOMREG_SHIFT */
          ParamExp exp;       /* cas IND_EXP */
          int noreg2 ;        /* cas IND_NOMREG et IND_NOMREG_SHIFT */
          SigneParam signe; 
          ParamInstShift exp_shift ; /* cas IND_NOMREG_SHIFT */
      } indir ;

       /* cas liste de registres : P_REGS */
       int regs[16];

       /* cas expression shift : P_SHIFT */
       ParamInstShift exp_shift ;
    } u ; 
} ParamInst ;

/* paramètre de directives de réservation de donnée initialisée */

typedef struct {
   NatParamReserv nat ; /* PR_NOMBRE, PR_ETIQUETTE, PR_CHAINE */

   /* cas nombre */
   long nb ;
   /* cas etiquette */
   char *nom_etiq ;
   /* cas chaine */
   char *chaine ;
} ParamReserv ;

/* type d'une ligne stockée */

typedef struct {
   NatLigneLog nat ;
   union {
      /* cas etiquette : LL_ETIQ */
       char *nom_etiq ;

      /* cas equ : LL_CTE */
      /* .set etiquette, entier */
      struct {char* etiq ; int valcte ;} cte ;

      /* cas instruction : LL_INST */
      struct { char *mnemo ; champs_inst s_i ;
		 int nbp ; ParamInst p[4]; } uinst ; /* 4 parametres max */ 

      /* cas declaration de global : LL_EXPORT */
      char *nom_globl ;

      /* cas sectionnement : LL_SECT */
      NomZone sect;

      /* cas reservation non initialisee : LL_RESERV_N_INIT */
      struct { DirReserv dir ; int nboctets ; char* etiq; } urni ;

      /* cas reservation initialisee : LL_RESERV_INIT */
      struct { DirReserv dir ; ParamReserv p0 ; } uri ;

      /* cas alignement : LL_ALIGN */
      unsigned int align ;

      /* cas entry : rien de plus que la nature */
      /* cas end : rien de plus que la nature */
   } u ;
} LigneLog ;

typedef struct {
        long     ad_dans_zone ;
        NomZone  zone_cour    ;
        int      nl_source    ; /* num de ligne dans le source */
        LigneLog ligne        ;
        long     nb_bits      ;
} Elem ;

#define MAX_LIGNE_LOG 1000

typedef Elem UnProg [] ;
typedef struct _taillesDeSections {
   int theTextZone_nelem ;
   int theDataZone_nelem ;
   int theCharTable_size ;
   int theSymbolTable_nelem ;
} taillesDeSections ;
#define MAXSYMBOLS 1000

typedef enum {Local, Global} LocGlob ;

typedef struct _asymbol {
        unsigned long AdressInCharTable ;
        unsigned long Value ;
        NomZone Zone ;
        LocGlob portee ;
} Asymbol ;
