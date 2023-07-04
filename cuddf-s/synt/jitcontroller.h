#ifndef JITCONTROLLER_H_
#define JITCONTROLLER_H_

#include "synt.h"

static DdNode** justice_gar;
static DdNode** justice_asm;
static DdNode* sysTrans;
static DdNode* envTrans;
static DdNode* sysIni;
static DdNode* envIni;
DdNode* transitions;
DdNode* initial;

static DdNode**** mX;
static DdNode*** mY;
static DdNode* Z;
static int n;
static int m;
static int* ranks;

static int jx;
static int rx;
static int ix;

DdNode* prime(DdNode* bdd, CuddPairing* pairs);
DdNode* unprime(DdNode* bdd, CuddPairing* pairs);

extern void loadFixpoints(DdNode* fixpoints, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int* kindices, int kindicesSize, 
	int* ranks_arr, CuddPairing* pairs, DdNode* primeVars);
extern void loadTrans(DdNode* trans, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int utilindex);
extern void loadJustices(DdNode* justices, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int utilindex, int newn, int newm);
extern DdNode* nextStatesController(DdNode* current, DdNode* inputs, CuddPairing* pairs, DdNode* unprimeVars);
extern int initController(DdNode* current, CuddPairing* pairs);
extern void freeController();

int findNextRank(int j, int from, int to, DdNode* conjunct);

#endif /*JITCONTROLLER_H_*/