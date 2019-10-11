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
*	Implementation of the the GR1 game related functions from synt.h
*/

#include "synt.h"
#include "cuddInt.h"
#include <stdio.h>

/*
* Free the memory that was allocated in gr1_game
*/
void free_gr1_mem()
{
	if (gr1_mem.x_mem != NULL || gr1_mem.y_mem != NULL) {
		for (int i = 0; i < gr1_mem.sizeD1; i++)
		{
			if (gr1_mem.x_mem != NULL) {
				for (int j = 0; j < gr1_mem.sizeD2; j++)
				{
					free(gr1_mem.x_mem[i][j]);
				}
				free(gr1_mem.x_mem[i]);
			}
			
			if (gr1_mem.y_mem != NULL) free(gr1_mem.y_mem[i]);
		}
		
		if (gr1_mem.x_mem != NULL) free(gr1_mem.x_mem);
		if (gr1_mem.y_mem != NULL) free(gr1_mem.y_mem);
		
		gr1_mem.x_mem = NULL;
		gr1_mem.y_mem = NULL;
	}

	if (gr1_mem.sizeD3 != NULL)
	{
		free(gr1_mem.sizeD3);
		gr1_mem.sizeD3 = NULL;
	}

	if (gr1_mem.z_mem != NULL)
	{
		free(gr1_mem.z_mem);
		gr1_mem.z_mem = NULL;
	}

	if (gr1_mem.z_mem_first_itr != NULL)
	{
		free(gr1_mem.z_mem_first_itr);
		gr1_mem.z_mem_first_itr = NULL;
	}
}

/*
* The set of states from which the system can force the environment to reach a state in "to".
*/
DdNode* yield_orig(DdNode* toPrime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs, DdNode* sysTrans, DdNode* envTrans, int sca)
{
	DdNode* statesSysTransTo;
	
	if (sca) {
		// use simultaneous conjunction and abstraction
		statesSysTransTo = Cudd_bddAndAbstract(manager, toPrime, sysTrans, sysPrimeVars);
		Cudd_Ref(statesSysTransTo);
	}
	else {
		DdNode* sysTransTo = Cudd_bddAnd(manager, toPrime, sysTrans);
		Cudd_Ref(sysTransTo);

		statesSysTransTo = Cudd_bddExistAbstract(manager, sysTransTo, sysPrimeVars);
		Cudd_Ref(statesSysTransTo);

		Cudd_RecursiveDeref(manager, sysTransTo);
	}

	DdNode* illegalEnvTrans = Cudd_Not(envTrans);
	Cudd_Ref(illegalEnvTrans);
	DdNode* illegalTransOrStatesSysTransTo = Cudd_bddOr(manager, illegalEnvTrans, statesSysTransTo);
	Cudd_Ref(illegalTransOrStatesSysTransTo);
	Cudd_RecursiveDeref(manager, illegalEnvTrans);

	DdNode* yieldStates = Cudd_bddUnivAbstract(manager, illegalTransOrStatesSysTransTo, envPrimeVars);
	Cudd_Ref(yieldStates);

	Cudd_RecursiveDeref(manager, toPrime);
	Cudd_RecursiveDeref(manager, statesSysTransTo);
	Cudd_RecursiveDeref(manager, illegalTransOrStatesSysTransTo);

	return yieldStates;
}

DdNode* yield(DdNode* to, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs, DdNode* sysTrans, DdNode* envTrans, int sca)
{
	int n;
	unsigned int *arr;
	int varnum = Cudd_ReadSize(manager);
	arr = (unsigned int*)malloc(sizeof(unsigned int)*varnum);
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

	if (!sys_trans_quant_list.isInit || !env_trans_quant_list.isInit) {
		return yield_orig(toPrime, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
	}

	////printf("using yield with transQuantList\n");

	//for (int i = 0; i < responder_transQuantList.size(); i++) {
	//	BDD tmp = res. and (responder_transQuantList.get(i).partTrans);
	//	res.free();
	//	res = tmp.exist(responder_transQuantList.get(i).quantSet);
	//	tmp.free();
	//}

	//TODO: use Cudd_bddAndAbstract
	DdNode* yieldStates = toPrime;

	for (int i = 0; i < sys_trans_quant_list.listSize; i++) {
		if (sca) {
			// use simultaneous conjuction and abstraction
			DdNode* tmp = yieldStates;
			//Cudd_Ref(tmp);
			//Cudd_RecursiveDeref(manager, yieldStates);
			yieldStates = Cudd_bddAndAbstract(manager, tmp, sys_trans_quant_list.transList[i], sys_trans_quant_list.quantSets[i]);
			Cudd_Ref(yieldStates);
			Cudd_RecursiveDeref(manager, tmp);
		}
		else {
			DdNode* tmp = Cudd_bddAnd(manager, yieldStates, sys_trans_quant_list.transList[i]);
			Cudd_Ref(tmp);
			Cudd_RecursiveDeref(manager, yieldStates);
			yieldStates = Cudd_bddExistAbstract(manager, tmp, sys_trans_quant_list.quantSets[i]);
			Cudd_Ref(yieldStates);
			Cudd_RecursiveDeref(manager, tmp);
		}
	}

	//for (int i = 0; i < this.transQuantList.size(); i++) {
	//	BDD tmp = this.transQuantList.get(i).partTrans.imp(res);
	//	res.free();
	//	res = tmp.forAll(this.transQuantList.get(i).quantSet);
	//	tmp.free();
	//}

	for (int i = 0; i < env_trans_quant_list.listSize; i++) {
		DdNode* illegalEnvTrans = Cudd_Not(env_trans_quant_list.transList[i]);
		Cudd_Ref(illegalEnvTrans);
		
		DdNode* transImpYield = Cudd_bddOr(manager, illegalEnvTrans, yieldStates);
		Cudd_Ref(transImpYield);
		Cudd_RecursiveDeref(manager, illegalEnvTrans);
		Cudd_RecursiveDeref(manager, yieldStates);
		
		yieldStates = Cudd_bddUnivAbstract(manager, transImpYield, env_trans_quant_list.quantSets[i]);
		Cudd_Ref(yieldStates);
		Cudd_RecursiveDeref(manager, transImpYield);
	}

	//DdNode* yieldStates2 = yield2(to, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans);
	//int isYieldStatesEq = IS_BDD_EQ(yieldStates, yieldStates2);
	////printf("isYieldStatesEq = %d (true = %d, false = %d)\n", isYieldStatesEq, true, false);
	//fflush(stdout);
	//Cudd_RecursiveDeref(manager, yieldStates2);

	return yieldStates;
}
/*
* Check whether the system player wins from all initial states if winSys are its winning states
*/
int sysWinAllInitial(DdNode* winSys, DdNode* sysIni, DdNode* envIni,
	DdNode* sysUnprimeVars, DdNode* envUnprimeVars)
{
	DdNode* sysWin = Cudd_bddAnd(manager, winSys, sysIni);
	Cudd_Ref(Cudd_Regular(sysWin));

	DdNode* sysWinExists = Cudd_bddExistAbstract(manager, sysWin, sysUnprimeVars);
	Cudd_Ref(Cudd_Regular(sysWinExists));

	DdNode* envIniNot = Cudd_Not(envIni);
	Cudd_Ref(Cudd_Regular(envIniNot));

	DdNode* sysWinFromInis = Cudd_bddOr(manager, envIniNot, sysWinExists);
	Cudd_Ref(Cudd_Regular(sysWinFromInis));
	Cudd_RecursiveDeref(manager, envIniNot);

	DdNode* sysWinFromInisForAllEnvIni = Cudd_bddUnivAbstract(manager, sysWinFromInis, envUnprimeVars);
	Cudd_Ref(Cudd_Regular(sysWinFromInisForAllEnvIni));

	int allIni = (sysWinFromInisForAllEnvIni == Cudd_ReadOne(manager));
	////printf("allIni = %d\n", allIni);

	Cudd_RecursiveDeref(manager, sysWin);
	Cudd_RecursiveDeref(manager, sysWinExists);
	Cudd_RecursiveDeref(manager, sysWinFromInis);
	Cudd_RecursiveDeref(manager, sysWinFromInisForAllEnvIni);

	return allIni;
}

void extend_size_2D(DdNode*** in, int sizeD1, int newSize)
{
	int size1 = sizeof(in);
	DdNode** res;
	//printf("extend_size_2D: newSize = %d\n", newSize);
	for (int i = 0; i < sizeD1; i++) {
		res = realloc(in[i], newSize * sizeof(DdNode*));
		if (res == NULL) {
			//printf("ERROR: can't realloc in extend_size_2D!\n");
			fflush(stdout);
			return;
		}

		in[i] = res;
	}
	//printf("extend_size_2D end\n");
}

void copy_to_gr1_mem(inc_gr1_data inc_data, int x_currSize)
{
	//printf("copy_to_gr1_mem\n");
	
	gr1_mem.sizeD3 = malloc(inc_data.sizeD1 * sizeof(int));
	memcpy(gr1_mem.sizeD3, inc_data.sizeD3, inc_data.sizeD1 * sizeof(int));

	for (int j = 0; j < inc_data.sizeD1; j++)
	{
		gr1_mem.z_mem[j] = inc_data.z_mem[j];
		Cudd_Ref(Cudd_Regular(gr1_mem.z_mem[j]));

		gr1_mem.z_mem_first_itr[j] = inc_data.z_mem_first_itr[j];
		Cudd_Ref(Cudd_Regular(gr1_mem.z_mem_first_itr[j]));

		for (int i = 0; i < inc_data.sizeD2; i++)
		{
			if (x_currSize <= inc_data.sizeD3[j])
			{
				gr1_mem.x_mem[j][i] = realloc(gr1_mem.x_mem[j][i], inc_data.sizeD3[j] * sizeof(DdNode*));
				if (gr1_mem.x_mem[j][i] == NULL) {
					//printf("ERROR: can't realloc in gr1_mem.x_mem[%d][%d]!\n", j, i);
					fflush(stdout);
					return;
				}
			}
			for (int cy = 0; cy < inc_data.sizeD3[j]; cy++)
			{
				//TODO: TMP
				gr1_mem.x_mem[j][i][cy] = inc_data.x_mem[j][i][cy];
				//gr1_mem.x_mem[j][i][cy] = Cudd_ReadOne(manager);
				Cudd_Ref(Cudd_Regular(gr1_mem.x_mem[j][i][cy]));
			}
		}
		
		// initialize gr1_mem.y_mem to Zero BDD, so there will be no problems when retrieving yMem from java 
		if (x_currSize <= inc_data.sizeD3[j])
		{
			gr1_mem.y_mem[j] = realloc(gr1_mem.y_mem[j], inc_data.sizeD3[j] * sizeof(DdNode*));
			if (gr1_mem.y_mem[j] == NULL) {
				//printf("ERROR: can't realloc in gr1_mem.y_mem[%d]!\n", j);
				fflush(stdout);
				return;
			}
		}
		for (int cy = 0; cy < inc_data.sizeD3[j]; cy++)
		{
			gr1_mem.y_mem[j][cy] = Cudd_Not(Cudd_ReadOne(manager));
			Cudd_Ref(Cudd_Regular(gr1_mem.y_mem[j][cy]));
		}
	}
}

void handle_inc_guar_added(inc_gr1_data inc_data, int sysJSize, int * j_start_idx, DdNode** z, int currSize, int * cy_mem)
{
	if (IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_NEW_JUSTICE_ADDED)
		&& !IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_NEW_SAFETY_ADDED)
		&& (sysJSize != 1))
	{
		//printf("New justice(s) was added, to an existing list of justices. Current num of sys justices is %d\n", sysJSize);
		*j_start_idx = inc_data.sizeD1;
		//printf("New justice was added, starting from j_start_idx = %d\n", *j_start_idx);
		copy_to_gr1_mem(inc_data, currSize);
		for (int i = 0; i < inc_data.sizeD1; i++)
		{
			cy_mem[i] = inc_data.sizeD3[i];
		}
		free(gr1_mem.sizeD3);
		
		*z = inc_data.z_mem[inc_data.sizeD1 - 1];
		Cudd_Ref(Cudd_Regular(*z));

		//printf("New justice was added, starting from z is one = %d\n", (z == Cudd_ReadOne(manager)));
	} else if (IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_NEW_JUSTICE_ADDED) 
		|| IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_NEW_SAFETY_ADDED))
	{
		//printf("use inc_data.start_z\n");
		*z = inc_data.start_z;
		Cudd_Ref(Cudd_Regular(*z));
	}

	//printf("is starting Z from One = %d\n", (z == Cudd_ReadOne(manager)));
}

void handle_inc_only_j_removed(inc_gr1_data inc_data, int * j_start_idx, DdNode** z, int x_currSize, int * cy_mem)
{
	if (!IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_PREV_SAFETY_REMOVED)
		&& IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_PREV_JUSTICE_REMOVED)
		&& inc_data.least_removed_justice > 0)
	{
		//printf("previous justice was removed, inc_data.least_removed_justice = %d\n", inc_data.least_removed_justice);
		for (int k = 0; k < inc_data.least_removed_justice; k++)
		{
			gr1_mem.z_mem[k] = inc_data.z_mem_first_itr[k];
			Cudd_Ref(Cudd_Regular(gr1_mem.z_mem[k]));

			gr1_mem.z_mem_first_itr[k] = inc_data.z_mem_first_itr[k];
			Cudd_Ref(Cudd_Regular(gr1_mem.z_mem_first_itr[k]));

			cy_mem[k] = inc_data.sizeD3[k];

			for (int i = 0; i < inc_data.sizeD2; i++)
			{
				if (x_currSize <= inc_data.sizeD3[k])
				{
					gr1_mem.x_mem[k][i] = realloc(gr1_mem.x_mem[k][i], inc_data.sizeD3[k] * sizeof(DdNode*));
					if (gr1_mem.x_mem[k][i] == NULL) {
						//printf("ERROR: can't realloc in gr1_mem.x_mem[%d][%d]!\n", k, i);
						fflush(stdout);
						return;
					}
				}

				for (int cy = 0; cy < inc_data.sizeD3[k]; cy++)
				{
					//TODO: TMP
					gr1_mem.x_mem[k][i][cy] = inc_data.x_mem[k][i][cy];
					//gr1_mem.x_mem[k][i][cy] = Cudd_ReadOne(manager);
					Cudd_Ref(Cudd_Regular(gr1_mem.x_mem[k][i][cy]));
				}
			}
			// initialize gr1_mem.y_mem to Zero BDD, so there will be no problems when retrieving yMem from java 
			if (x_currSize <= inc_data.sizeD3[k])
			{
				gr1_mem.y_mem[k] = realloc(gr1_mem.y_mem[k], inc_data.sizeD3[k] * sizeof(DdNode*));
				if (gr1_mem.y_mem[k] == NULL) {
					//printf("ERROR: can't realloc in gr1_mem.y_mem[%d]!\n", k);
					fflush(stdout);
					return;
				}
			}
			for (int cy = 0; cy < inc_data.sizeD3[k]; cy++)
			{
				gr1_mem.y_mem[k][cy] = Cudd_Not(Cudd_ReadOne(manager));
				Cudd_Ref(Cudd_Regular(gr1_mem.y_mem[k][cy]));
			}
		}
		FREE_BDD(*z);
		*z = gr1_mem.z_mem_first_itr[inc_data.least_removed_justice - 1];
		Cudd_Ref(Cudd_Regular(*z));
		*j_start_idx = inc_data.least_removed_justice;
		//printf("starting first z iteration from j_start_idx = %d\n", *j_start_idx);
	}
}

void handle_inc_only_safety_removed(inc_gr1_data inc_data, int j, DdNode** y)
{
	if (IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_PREV_SAFETY_REMOVED)
		&& !IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_PREV_JUSTICE_REMOVED))
	{
		//printf("use inc_data.z_mem[%d] for current start Y\n", j);
		FREE_BDD(*y);
		*y = inc_data.z_mem[j];
		Cudd_Ref(Cudd_Regular(*y));

		if (*y == Cudd_Not(Cudd_ReadOne(manager)))
		{
			//printf("start Y (for j=%d) is zero \n", j);
		}
	}
}

void handle_inc_safety_added(inc_gr1_data inc_data, int j, int i, int cy, DdNode** x, DdNode* z)
{
	if (IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_NEW_SAFETY_ADDED) && j < inc_data.sizeD1) {
		//printf("use inc_data.x_mem[%d][%d][%d] for current X\n", j, i, cy);
		int k = cy;
		if (inc_data.sizeD3[j] <= cy)
		{
			//printf("\tinc_data.sizeD3[%d] (%d) <= cy (%d) \n", j, inc_data.sizeD3[j], cy);
			k = inc_data.sizeD3[j] - 1;
		}
		*x = Cudd_bddAnd(manager, inc_data.x_mem[j][i][k], z);
	}
	else {
		*x = z;
	}

	Cudd_Ref(Cudd_Regular(*x));
}
int gr1_game(DdNode** sysJ, int sysJSize, DdNode** envJ, int envJSize, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysUnprime, DdNode* envUnprime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	int efp, int eun, int fpr, int sca)
{
	inc_gr1_data inc_data;

	//int i;
	//for (i = 0; i < sysJSize; i++)
	//{
	//	//printf("sysJ[%d] = %d\n", i, sysJ[i]->index); fflush(stdout);
	//}
	//for (i = 0; i < envJSize; i++)
	//{
	//	//printf("envJ[%d] = %d\n", i, envJ[i]->index); fflush(stdout);
	//}

	////printf("sysTrans = %d\n", sysTrans->index);
	////printf("envTrans = %d\n", envTrans->index);
	////printf("sysPrimeVars = %d\n", sysPrimeVars->index);
	////printf("envPrimeVars = %d\n", envPrimeVars->index);

	//DdNode* yieldStates = yield(Cudd_Not(Cudd_ReadOne(manager)), sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans);
	////printf("yieldStates = %d\n", yieldStates->index);

	return gr1_game_inc(sysJ, sysJSize, envJ, envJSize, sysIni, envIni, sysTrans, envTrans,
		sysUnprime, envUnprime, sysPrimeVars, envPrimeVars, pairs,
		efp, eun, fpr, sca, false, inc_data);
}

int gr1_game_inc(DdNode** sysJ, int sysJSize, DdNode** envJ, int envJSize, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysUnprime, DdNode* envUnprime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	int efp, int eun, int fpr, int sca, int isInc, inc_gr1_data inc_data)
{
	//printf("\n----Start GR1 Game: efp=%d, eun=%d, fpr=%d----\n", efp, eun, fpr);
	if (isInc) print_inc_type(inc_data.type_bitmap);

	//printf("sysJSize=%d, envJSize=%d\n", sysJSize, envJSize);
	gr1_mem.sizeD1 = sysJSize;
	gr1_mem.sizeD2 = envJSize;

	int currSize = 50;
	gr1_mem.x_mem = malloc(sysJSize * sizeof(DdNode***));
	gr1_mem.y_mem = malloc(sysJSize * sizeof(DdNode**));
	gr1_mem.z_mem = malloc(sysJSize * sizeof(DdNode*));
	for (int sysJi = 0; sysJi < sysJSize; sysJi++)
	{
		gr1_mem.x_mem[sysJi] = malloc(envJSize * sizeof(DdNode**));
		for (int envJi = 0; envJi < envJSize; envJi++)
		{
			gr1_mem.x_mem[sysJi][envJi] = malloc(currSize * sizeof(DdNode*));
		}
		gr1_mem.y_mem[sysJi] = malloc(currSize * sizeof(DdNode*));
	}

	if (isInc) {
		gr1_mem.z_mem_first_itr = malloc(sysJSize * sizeof(DdNode*));
	}
	else {
		gr1_mem.z_mem_first_itr = NULL;
	}

	DdNode *x = NULL, *y, *z;
	DdNode *xPrev, *yPrev, *zPrev;

	int * cy_mem = malloc(sysJSize * sizeof(int));
	memset(cy_mem, -1, sysJSize * sizeof(int));
	int cy = 0; // count y
	int firstZIter = true;

	//First - Z fixed point
	z = Cudd_ReadOne(manager);
	Cudd_Ref(Cudd_Regular(z));
	zPrev = NULL;
	yPrev = NULL;
	int j_start_idx = 0;

	////printf("Z loop - before\n");
	//Cudd_DebugCheck(manager);
	//Cudd_CheckKeys(manager);

	int zIters = 0;
	int yIters = 0;
	int xIters = 0;

	int xtmp = 0;
	int ytmp = 0;

	int isFinished = false;

	if (isInc && is_inc_only_ini(inc_data.type_bitmap))
	{
		//printf("Only ini states changed\n");
		z = inc_data.z_mem[sysJSize - 1];	
		int is_real = sysWinAllInitial(z, sysIni, envIni, sysUnprime, envUnprime);
		copy_to_gr1_mem(inc_data, currSize);

		//printf("End GR1 Game: is realizable = %d\n", is_real);
		return is_real;
	}

	if (isInc) handle_inc_guar_added(inc_data, sysJSize, &j_start_idx, &z, currSize, cy_mem);

	while (zPrev == NULL || !IS_BDD_EQ(z, zPrev))
	{
		zIters++;

		//if (zPrev == NULL) //printf("zPrev is NULL\n");
		//if (zPrev != NULL) //printf("IS_BDD_EQ(z, zPrev) = %d\n", IS_BDD_EQ(z, zPrev));

		FREE_BDD(zPrev);
		zPrev = z;
		Cudd_Ref(zPrev);

		//TODO: TMP - can handle justice removes without xMem
		if (isInc && firstZIter) handle_inc_only_j_removed(inc_data, &j_start_idx, &z,currSize, cy_mem);

		for (int j = j_start_idx; j < sysJSize; j++)
		{
			//printf("Z loop %d: j = %d\n", zIters, j); 
			//fflush(stdout);
			//Cudd_DebugCheck(manager);
			//Cudd_CheckKeys(manager);
			
			cy = 0;
			y = Cudd_Not(Cudd_ReadOne(manager));
			Cudd_Ref(y);

			FREE_BDD(yPrev);
			DdNode* yieldStatesZ = yield(z, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
			DdNode* yieldStatesZToJ = Cudd_bddAnd(manager, sysJ[j], yieldStatesZ);
			Cudd_Ref(yieldStatesZToJ);
			FREE_BDD(yieldStatesZ);
			if (isInc) handle_inc_only_safety_removed(inc_data, j, &y);
			yPrev = NULL;
			//Second - Y fixed point 
			while (yPrev == NULL || !IS_BDD_EQ(y, yPrev))
			{
				yIters++;
				ytmp++;
				////printf("y iterations = %d\, isFalse = %d \n", ytmp, y == Cudd_Not(Cudd_ReadOne(manager))); fflush(stdout);
				////printf("Y loop - start\n"); fflush(stdout);
				//Cudd_DebugCheck(manager);
				//Cudd_CheckKeys(manager);

				FREE_BDD(yPrev);
				yPrev = y;
				Cudd_Ref(yPrev);

				////printf("Y loop - before yieldStatesY \n"); fflush(stdout);
				//Cudd_DebugCheck(manager);
				//Cudd_CheckKeys(manager);

				DdNode* yieldStatesY = yield(y, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
				DdNode* start = Cudd_bddOr(manager, yieldStatesZToJ, yieldStatesY);
				Cudd_Ref(start);
				FREE_BDD(yieldStatesY);

				////printf("Y loop - before env loop \n"); fflush(stdout);
				//Cudd_DebugCheck(manager);
				//Cudd_CheckKeys(manager);

				FREE_BDD(y);
				y = Cudd_Not(Cudd_ReadOne(manager));
				Cudd_Ref(y);

				for (int i = 0; i < envJSize; i++)
				{
					////printf("Y loop - i = %d\n", i); fflush(stdout);
					//Cudd_DebugCheck(manager);
					//Cudd_CheckKeys(manager);

					DdNode* negEnvJ = Cudd_Not(envJ[i]);
					Cudd_Ref(negEnvJ);
					FREE_BDD(x);

					if (isInc) handle_inc_safety_added(inc_data, j, i, cy, &x, z);

					if (fpr && !firstZIter)
					{
						int rcy = -1;
						if (cy < cy_mem[j])
						{
							rcy = cy;
						}
						
						if (!isInc) {
							if (rcy == -1) {
								x = z;
								Cudd_Ref(x);
							} else {
								//printf("recycleFixPoint X for j=%d, i=%d, rcy=%d\n", j, i, rcy);
								x = Cudd_bddAnd(manager, gr1_mem.x_mem[j][i][rcy], z);
								Cudd_Ref(x);
							}
						} else if (rcy != -1) {
							//printf("recycleFixPoint X for j=%d, i=%d, rcy=%d\n", j, i, rcy);
							DdNode* tmp = Cudd_bddAnd(manager, gr1_mem.x_mem[j][i][rcy], x);
							Cudd_Ref(tmp);
							FREE_BDD(x);
							x = tmp;
						}
					} else if (!isInc) {
						x = z;
						Cudd_Ref(x);
					}

					xPrev = NULL;
					// Third - X fixed point
					while (xPrev == NULL || !IS_BDD_EQ(x, xPrev))
					{
						xIters++;
						xtmp++;
						////printf("X loop - start\n"); fflush(stdout);
						//Cudd_DebugCheck(manager);
						//Cudd_CheckKeys(manager);

						FREE_BDD(xPrev);
						xPrev = x;
						////printf("is x one = %d\n", x == Cudd_ReadOne(manager)); fflush(stdout);
						////printf("is xPrev one = %d\n", xPrev == Cudd_ReadOne(manager)); fflush(stdout);
						Cudd_Ref(xPrev);
						DdNode* yieldStatesX = yield(x, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
						DdNode* yieldStatesXnotToJ = Cudd_bddAnd(manager, yieldStatesX, negEnvJ);
						Cudd_Ref(yieldStatesXnotToJ);
						FREE_BDD(yieldStatesX);
						
						FREE_BDD(x);
						x = Cudd_bddOr(manager, yieldStatesXnotToJ, start);
						Cudd_Ref(x);
						
						FREE_BDD(yieldStatesXnotToJ);
					} // End X fixed point
					////printf("xtmp = %d\n", xtmp);
					xtmp = 0;
					FREE_BDD(xPrev);
					FREE_BDD(negEnvJ);
					////printf("j = %d, i = %d, cy = %d\n", j,i,cy); fflush(stdout);
					////printf("cy = %d, cy_mem[%d] = %d\n", cy,j, cy_mem[j]); fflush(stdout);
					if (cy < cy_mem[j]) {
						FREE_BDD(gr1_mem.x_mem[j][i][cy]);
					}
					gr1_mem.x_mem[j][i][cy] = x;
					Cudd_Ref(gr1_mem.x_mem[j][i][cy]);

					DdNode* tmp = Cudd_bddOr(manager, y, x);
					Cudd_Ref(tmp);
					FREE_BDD(y);
					y = tmp;

				} // End loop over envJ
				////printf("j = %d, cy = %d\n", j,cy); fflush(stdout);
				FREE_BDD(start);
				if (cy < cy_mem[j]) {
					FREE_BDD(gr1_mem.y_mem[j][cy]);
				}

				gr1_mem.y_mem[j][cy] = y;
				Cudd_Ref(gr1_mem.y_mem[j][cy]);

				cy++;
				// extend size of x_mem and y_mem
				if (cy == currSize) {
					currSize = currSize * 2;
					extend_size_3D(gr1_mem.x_mem, sysJSize, envJSize, currSize);
					extend_size_2D(gr1_mem.y_mem, sysJSize, currSize);
				}

				////printf("IS_BDD_EQ(y, yPrev) = %d\n", IS_BDD_EQ(y, yPrev));
			} // End Y fixed point
			FREE_BDD(yieldStatesZToJ);
			FREE_BDD(z);
			z = y;

			////printf("ytmp = %d\n", ytmp);
			ytmp = 0;

			if (eun && !sysWinAllInitial(z, sysIni, envIni, sysUnprime, envUnprime)) {
				//printf("sysWinAllInitial is false - detected early unrealizable\n");
				z = Cudd_Not(Cudd_ReadOne(manager));
				isFinished = true;
				break;
			}

			if (efp && !firstZIter) {
				////printf("firstZIter = %d\n", firstZIter);
				if (IS_BDD_EQ(gr1_mem.z_mem[j], z)) {
					//printf("detected early fixed point\n");
					FREE_BDD(z);
					z = gr1_mem.z_mem[sysJSize - 1];
					isFinished = true;
					break;
				}
			}

			//TODO: for each i save the last x_mem[j][i][cy_mem[j]] 
			cy_mem[j] = cy;
			gr1_mem.z_mem[j] = z;
			Cudd_Ref(gr1_mem.z_mem[j]);
			if (firstZIter && isInc)
			{
				//printf("set gr1_mem.z_mem_first_itr[%d]\n",j);
				gr1_mem.z_mem_first_itr[j] = z;
				Cudd_Ref(gr1_mem.z_mem_first_itr[j]);
			}

		} // End loop over sysJ

		j_start_idx = 0;
		firstZIter = false;
		////printf("zPrev == NULL = %d\n", (zPrev == NULL));
		////printf("IS_BDD_EQ(z, zPrev) = %d\n", IS_BDD_EQ(z, zPrev));
		if (isFinished) break;

	} // End Z fixed point
	
	FREE_BDD(zPrev);
	FREE_BDD(x);
	
	// reduce size for x_mem and y_mem if needed.
	////printf("before sizeD3 malloc\n");
	gr1_mem.sizeD3 = malloc(sysJSize * sizeof(int));
	memcpy(gr1_mem.sizeD3, cy_mem, sysJSize * sizeof(int));
	free(cy_mem);
	cy_mem = NULL;
	//for (int i = 0; i < sysJSize; i++)
	//{
	//	//printf("sizeD3[%d] = %d\n", i,gr1_mem.sizeD3[i]);
	//	//printf("cy_mem[%d] = %d\n", i, cy_mem[i]);
	//}

	//printf("z iterations = %d\n", zIters);
	//printf("y iterations = %d\n", yIters);
	//printf("x iterations = %d\n", xIters);

	int is_real = sysWinAllInitial(z, sysIni, envIni, sysUnprime, envUnprime);
	//printf("End GR1 Game: is realizable = %d\n", is_real);

	//Cudd_DebugCheck(manager);
	//Cudd_CheckKeys(manager);
	//fflush(stdout);

	return is_real;
}
