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