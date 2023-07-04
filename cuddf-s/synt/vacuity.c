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


#include "synt.h"
#include "cuddInt.h"
#include <stdio.h>


/*
* The set of states from which the system and environment can together reach "toPrime" in a single step
*/

DdNode* vacuity_prev(DdNode* to, DdNode* primeVars, CuddPairing* pairs, DdNode* trans)
{
	int n;
	unsigned int* arr;
	int varnum = Cudd_ReadSize(manager);
	arr = (unsigned int*)malloc(sizeof(unsigned int) * varnum);
	if (arr == NULL) {
		//printf("couldn't allocate array of uint of size %d\n", varnum);
		fflush(stdout);
		return INVALID_BDD;
	}
	for (n = 0; n < varnum; ++n) {
		DdNode* node = pairs->table[n];
		unsigned int var = Cudd_NodeReadIndex(node);
		arr[n] = var;
	}
	DdNode* toPrime = Cudd_bddPermute(manager, to, arr);
	Cudd_Ref(toPrime);
	free(arr);

	DdNode* transAndTo = Cudd_bddAnd(manager, trans, toPrime);
	Cudd_Ref(transAndTo);
	DdNode* result = Cudd_bddExistAbstract(manager, transAndTo, primeVars);
	Cudd_Ref(result);
	Cudd_RecursiveDeref(manager, transAndTo);
	Cudd_RecursiveDeref(manager, toPrime);
	return result;
}
DdNode* reachability(DdNode* to, DdNode* primeVars, CuddPairing* pairs, DdNode* trans)
{
	DdNode* attr;
	DdNode* attr_prev;
	attr = Cudd_Not(Cudd_ReadOne(manager));
	Cudd_Ref(Cudd_Regular(attr));
	attr_prev = NULL;

	while (attr_prev == NULL || !IS_BDD_EQ(attr, attr_prev)) 
	{
		FREE_BDD(attr_prev);
		attr_prev = attr;
		Cudd_Ref(attr_prev);

		DdNode* pred = vacuity_prev(attr, primeVars, pairs, trans);
		FREE_BDD(attr);
		attr = Cudd_bddOr(manager, pred, to);
		Cudd_Ref(attr);
		FREE_BDD(pred);
	}
	FREE_BDD(attr_prev);

	return attr;
}


DdNode* buchi(DdNode** targets, int targetsSize, DdNode* primeVars, CuddPairing* pairs, DdNode* trans) 
{
	DdNode* zero = Cudd_Not(Cudd_ReadOne(manager));
	Cudd_Ref(Cudd_Regular(zero));
	if (IS_BDD_EQ(trans, zero)) {
		return zero;
	}
	FREE_BDD(zero);
	DdNode* z;
	DdNode* z_prev;
	z = Cudd_ReadOne(manager);
	Cudd_Ref(Cudd_Regular(z));
	z_prev = NULL;
	while (z_prev == NULL || !IS_BDD_EQ(z, z_prev)) {
		FREE_BDD(z_prev);
		z_prev = z;
		Cudd_Ref(z_prev);
		for (int i = 0; i < targetsSize; i++) {
			DdNode* currentTarget = targets[i];
			DdNode* pred = vacuity_prev(z, primeVars, pairs, trans);
			DdNode* start = Cudd_bddAnd(manager, currentTarget, pred);
			Cudd_Ref(start);
			FREE_BDD(pred);
			DdNode* reachBwd = reachability(start, primeVars, pairs, trans);
			FREE_BDD(start);
			DdNode* nextZ = Cudd_bddAnd(manager, z, reachBwd);
			Cudd_Ref(nextZ);
			FREE_BDD(reachBwd);
			FREE_BDD(z);
			z = nextZ;
			Cudd_Ref(z);
			FREE_BDD(nextZ);
		}
	}
	FREE_BDD(z_prev);
	return z;
}

int intersectionNotEmpty(DdNode* a, DdNode* b)
{
	DdNode* zero = Cudd_Not(Cudd_ReadOne(manager));
	Cudd_Ref(Cudd_Regular(zero));

	DdNode* both = Cudd_bddAnd(manager, a, b);
	Cudd_Ref(both);
	int ans = !IS_BDD_EQ(both, zero);
	FREE_BDD(zero);
	FREE_BDD(both);
	return ans;
}

int canReach(DdNode* target, DdNode* from, DdNode* primeVars, CuddPairing* pairs, DdNode* trans)
{

	int hasReached = intersectionNotEmpty(target, from);
	DdNode* attr;
	DdNode* attr_prev;
	attr = Cudd_Not(Cudd_ReadOne(manager));
	Cudd_Ref(Cudd_Regular(attr));
	attr_prev = NULL;

	while (!hasReached && (attr_prev == NULL || !IS_BDD_EQ(attr, attr_prev)))
	{
		FREE_BDD(attr_prev);
		attr_prev = attr;
		Cudd_Ref(attr_prev);

		DdNode* pred = vacuity_prev(attr, primeVars, pairs, trans);
		FREE_BDD(attr);
		attr = Cudd_bddOr(manager, pred, from);
		Cudd_Ref(attr);
		FREE_BDD(pred);
		hasReached = intersectionNotEmpty(target, attr);
	}
	FREE_BDD(attr_prev);
	FREE_BDD(attr);
	return hasReached;
}

int checkJusticeImplication(DdNode* ini, DdNode* trans, DdNode** justices, int justiceNum, DdNode* targetJustice, DdNode* primeVars, CuddPairing* pairs)
{
	DdNode* notJust = Cudd_Not(targetJustice);
	Cudd_Ref(notJust);
	DdNode* newTrans = Cudd_bddAnd(manager, trans, notJust);
	Cudd_Ref(newTrans);
	FREE_BDD(notJust);
	DdNode* winWhileNotJust = buchi(justices, justiceNum, primeVars, pairs, newTrans);
	FREE_BDD(newTrans);
	int result = !canReach(ini, winWhileNotJust, primeVars, pairs, trans);
	FREE_BDD(winWhileNotJust);
	return result;
}