#ifndef __AVALANCHE_H
#define __AVALANCHE_H

enum
{
  BVLT,  //unsigned less
  BVGE,  //unsigned greater or equal
  IFT,   //equal
  IFNOT, //not equal
  BVLE,  //unsigned less or equal
  BVGT,  //unsigned greater
  SBVLT,  //signed less
  SBVGE,  //signed greater or equal
  SBVLE,  //signed less or equal
  SBVGT,  //signed greater
  INVALID
};

struct _fdsNode 
{
  struct _fdsNode* next;
  HWord key;  
  HChar* name;
  ULong offs;
  ULong size;
  Int seqnum;
};

typedef struct _fdsNode fdsNode; 

struct _stringNode
{
  struct _stringNode* next;
  HWord key;
  Bool declared;
  Char* filename;
  Int filenum;
};

typedef struct _stringNode stringNode;

struct _replaceData
{
  UChar* data;
  Int length;
};

typedef struct _replaceData replaceData;

struct _bbNode 
{
  struct _sizeNode* next;
  UWord key;  
};

typedef struct _bbNode bbNode;


struct _taintedNode
{
  struct _taintedNode* next;
  HWord key;
  HChar* filename;
  HWord offset;
  Char fileIndex;
};

typedef struct _taintedNode taintedNode;

struct _sizeNode
{
  struct _sizeNode* next;
  UWord key;
  UShort* tempSize;
  Int tempsnum;
  UInt visited;
};

typedef struct _sizeNode sizeNode;

HWord hashCode(Char* str);

#define WITH_AVALANCHE

#endif
