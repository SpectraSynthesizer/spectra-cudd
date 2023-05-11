/*
Copyright (c) since 2015, Tel Aviv University and Software Modeling Lab

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of Tel Aviv University and Software Modeling Lab nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL Tel Aviv University and Software Modeling Lab 
BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE 
GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) 
HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT 
LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT 
OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. 
*/

/*
*	SYNT project related parametrs and functions
*	This file in the file hirarchy above the CUDD related files:
*		it implements functions related to the SYNT project using the CUDD library, 
*		and called from the cudd_jni.c  
*/

#ifndef SYNT_H_
#define SYNT_H_

//#define _DEBUG
#define _CRTDBG_MAP_ALLOC  
#include <stdlib.h>  
//#include <crtdbg.h>  

#ifdef _WIN32
#include <windows.h>
#endif
#include <stdio.h>
#include "cudd.h"
#include "cuddInt.h"

#ifdef __cplusplus
extern "C" {
#endif

#define INVALID_BDD 0L
extern DdManager* manager;

typedef struct CuddPairing {
	DdNode** table;
	struct CuddPairing *next;
} CuddPairing;

static CuddPairing *pair_list;

#define true 1
#define false 0

#define IS_BDD_EQ(bdd1, bdd2) (Cudd_bddLeq(manager, bdd1, bdd2) == 1 && Cudd_bddLeq(manager, bdd2, bdd1) == 1)
#define FREE_BDD(bdd) freeBDD(bdd); bdd = NULL;

struct gr1Mem {
	DdNode**** x_mem;
	DdNode*** y_mem;
	DdNode** z_mem;
	DdNode** z_mem_first_itr;
	int sizeD1;
	int sizeD2;
	int * sizeD3;
};

struct gr1StarMem {
	DdNode**** x_mem;
	DdNode*** y_mem;
	DdNode** z_mem;

	DdNode*** fulfill_exist_mem;
	DdNode*** towards_exist_mem;
	DdNode*** envJ_violation_mem; //mapping each env justice to memory vector of size envJ_violation_sizeD2
	
	int exist_sizeD1; //exist gar num
	int* fulfill_exist_sizeD2; //number of iterations for each exist gar
	int* towards_exist_sizeD2; //number of iterations towards each exist gar
	
	int envJ_violation_sizeD2; //number of outermost l.f.p. iterations to compute env justice violation strategy

	int x_y_z_sizeD1; //sys justice num
	int x_sizeD2; //env justice num
	int* x_sizeD3; //number of Y iterations for each sys justice

	DdNode* sys_win; //the system's winning region in the GR(1)* game
};

struct rabinMem {
	DdNode**** x_mem;
	DdNode**** x_mem_recycle;
	DdNode** z_mem;
	int sizeD1;
	int xSizeD2;
	int ** sizeD3;
};

typedef enum INC_TYPE {
	INC_TYPE_NO_INC = 0,
	INC_TYPE_NEW_INI_ADDED = 1,
	INC_TYPE_NEW_SAFETY_ADDED =2,
	INC_TYPE_NEW_JUSTICE_ADDED = 4,
	INC_TYPE_PREV_INI_REMOVED = 8,
	INC_TYPE_PREV_SAFETY_REMOVED = 16,
	INC_TYPE_PREV_JUSTICE_REMOVED = 32
} inc_type;

#define IS_BIT_ON(bitmap, type) ((bitmap & type) == type)

typedef struct incrementalGr1Data {
	int type_bitmap;
	DdNode* start_z;
	DdNode**** x_mem;
	DdNode** z_mem;
	DdNode** z_mem_first_itr;
	int sizeD1;
	int sizeD2;
	int * sizeD3;
	int least_removed_justice;
} inc_gr1_data;

typedef struct incrementalRabinData {
	int type_bitmap;
	DdNode* start_z;
	DdNode**** x_mem;
	DdNode** z_mem;
	int sizeD1;
	int sizeD2;
	int ** sizeD3;
	int least_removed_justice;
} inc_rabin_data;

struct transQuantList {
	int isInit;
	int listSize;
	DdNode** transList;
	DdNode** quantSets;
};

struct existSfaGarList {
	int isInit;
	int listSize;
	DdNode** sfaIniList;
	DdNode** sfaTransList;
	DdNode** sfaTransToAccList;
	DdNode** sfaUnprimeStateVars;
	DdNode** sfaPrimedStateVars;
};

struct gr1Mem gr1_mem;
struct gr1StarMem gr1_star_mem;
struct rabinMem rabin_mem;
struct transQuantList sys_trans_quant_list;
struct transQuantList env_trans_quant_list;
struct existSfaGarList exist_gars_list;

extern DdNode* ithVarInteger(DdManager* manager, int* vars, int varNum, int value);
extern DdNode* getFixpointsBDD(DdManager* manager, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int* kindices, int kindicesSize);
extern DdNode* getTransBDD(DdManager* manager, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int utilindex);
extern DdNode* getJusticesBDD(DdManager* manager, DdNode** sysJ, DdNode** envJ, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int utilindex);

// GR(1)* functions
extern DdNode* getFulfillBDD(DdManager* manager, int* exjindices, int exjindicesSize, int* findices, int findicesSize);
extern DdNode* getTowardsBDD(DdManager* manager, int* exjindices, int exjindicesSize, int* tindices, int tindicesSize);
extern DdNode* getEnvViolationBDD(DdManager* manager, int* iindices, int iindicesSize, int* kindices, int kindicesSize);
extern DdNode* getFixpointsStarBDD(DdManager* manager, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int* kindices, int kindicesSize);
extern DdNode* getJusticesStarBDD(DdManager* manager, DdNode** sysJ, DdNode** envJ, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int utilindex);

extern void freeBDD(DdNode* bdd);
extern void extend_size_3D(DdNode**** in, int sizeD1, int sizeD2, int newSize);
extern void extend_size_2D(DdNode*** in, int sizeD1, int newSize);

extern DdNode* pred(DdNode* to, int existGarIdx, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs, DdNode* sysTrans, DdNode* envTrans, int sca);
extern DdNode* yield(DdNode* to, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs, DdNode* sysTrans, DdNode* envTrans, int sca);
extern int sysWinAllInitial(DdNode* winSys, DdNode* sysIni, DdNode* envIni, DdNode* sysUnprimeVars, DdNode* envUnprimeVars);
extern int gr1_game(DdNode** sysJ, int sysJSize, DdNode** envJ, int envJSize, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysUnprime, DdNode* envUnprime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	int efp, int eun, int fpr, int sca);
extern int gr1_game_inc(DdNode** sysJ, int sysJSize, DdNode** envJ, int envJSize, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysUnprime, DdNode* envUnprime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	int efp, int eun, int fpr, int sca, int isInc, inc_gr1_data inc_data);
extern void free_gr1_mem();

extern int rabin_game(DdNode** sysJ, int sysJSize, DdNode** envJ, int envJSize, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysUnprime, DdNode* envUnprime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	int efp, int eun, int fpr, int sca);
extern int rabin_game_inc(DdNode** sysJ, int sysJSize, DdNode** envJ, int envJSize, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysUnprime, DdNode* envUnprime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	int efp, int eun, int fpr, int sca, int isInc, inc_rabin_data inc_data);
extern void free_rabin_mem();

extern int gr1_star_game(DdNode** sysJ, int sysJSize, DdNode** envJ, int envJSize, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysUnprime, DdNode* envUnprime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	int efp, int eun, int fpr, int sca, int mem);
extern void free_gr1_star_mem();

extern int checkJusticeImplication(DdNode* ini, DdNode* trans, DdNode** justices, int justiceNum, DdNode* targetJustice, DdNode* primeVars, CuddPairing* pairs);

extern void print_inc_type(int type_bitmap);
int is_inc_only_ini(int type_bitmap);

#ifdef __cplusplus
}
#endif

#endif /*SYNT_H_*/
