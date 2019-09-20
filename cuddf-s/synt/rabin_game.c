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

/*
* Free the memory that was allocated in rabin game
*/
void free_rabin_mem()
{
	if (rabin_mem.x_mem != NULL && rabin_mem.z_mem != NULL && rabin_mem.sizeD3 != NULL) {
		for (int i = 0; i < rabin_mem.sizeD1; i++)
		{
			for (int j = 0; j < rabin_mem.xSizeD2; j++)
			{
				free(rabin_mem.x_mem[i][j]);
			}

			//for (int j = 0; j < rabin_mem.xSizeD2; j++)
			//{
			//	free(rabin_mem.z_mem[i][j]);
			//}

			free(rabin_mem.x_mem[i]);
			free(rabin_mem.sizeD3[i]);
		}
		free(rabin_mem.x_mem);
		free(rabin_mem.z_mem);
		free(rabin_mem.sizeD3);

		rabin_mem.x_mem = NULL;
		rabin_mem.z_mem = NULL;
		rabin_mem.sizeD3 = NULL;
	}		
}

void extend_size_1D_3D(DdNode***** in, int sizeD2, int sizeD3, int oldSize, int newSize)
{
	DdNode**** res;
	//printf("extend_size_1D_3D: oldSize=%d, newSize=%d\n", oldSize, newSize);
	res = malloc(newSize * sizeof(DdNode***));

	for (int i = 0; i < newSize; i++)
	{
		////printf("i = %d\n", i); fflush(stdout);
		res[i] = malloc(sizeD2 * sizeof(DdNode**));
		for (int j = 0; j < sizeD2; j++)
		{
			////printf("j = %d\n", j); fflush(stdout);
			if (i < oldSize)
			{
				res[i][j] = realloc((*in)[i][j], sizeD3 * sizeof(DdNode*));
			}
			else {
				res[i][j] = malloc(sizeD3 * sizeof(DdNode*));
			}
			
			if (res[i][j] == NULL) {
				//printf("ERROR: can't allocate in extend_size_1D_3D! i=%d, oldSize=%d\n", i, oldSize);
				fflush(stdout);
				return;
			}

			//free((*in)[i]);
		}
	}

	*in = res;
	//printf("extend_size_1D_3D end\n");
}

void extend_size_1D_2D(DdNode**** in, int sizeD2, int oldSize, int newSize)
{
	DdNode*** res;
	//printf("extend_size_1D_2D: newSize = %d\n", newSize);
	res = malloc(newSize * sizeof(DdNode**));

	for (int i = 0; i < oldSize; i++)
	{
		res[i] = realloc((*in)[i], sizeD2 * sizeof(DdNode*));
		if (res[i] == NULL) {
			//printf("ERROR: can't realloc in extend_size_1D_2D!");
			fflush(stdout);
			return;
		}
	}

	for (int i = oldSize; i < newSize; i++)
	{
		res[i] = malloc(sizeD2 * sizeof(DdNode*));
		if (res[i] == NULL) {
			//printf("ERROR: can't malloc in extend_size_1D_2D!");
			fflush(stdout);
			return;
		}
	}

	*in = res;
	//printf("extend_size_1D_2D end\n");
}

void extend_size_1D(DdNode*** in, int oldSize, int newSize)
{
	DdNode** res;
	//printf("extend_size_1D: newSize = %d\n", newSize);
	res = realloc((*in), newSize * sizeof(DdNode*));
	if (res == NULL) {
		//printf("ERROR: can't realloc in extend_size_1D!");
		fflush(stdout);
		return;
	}

	*in = res;
	//printf("extend_size_1D end\n");
}

void extend_size_1D_2D_int(int*** in, int sizeD2, int oldSize, int newSize)
{
	int** res;
	//printf("extend_size_1D_2D_int: newSize = %d\n", newSize);
	res = malloc(newSize * sizeof(int*));

	for (int i = 0; i < oldSize; i++)
	{	
		res[i] = realloc((*in)[i], sizeD2 * sizeof(int));
		if (res[i] == NULL) {
			//printf("ERROR: can't realloc in extend_size_1D_2D_int!");
			fflush(stdout);
			return;
		}
	}

	for (int i = oldSize; i < newSize; i++)
	{
		res[i] = malloc(sizeD2 * sizeof(int));
		if (res[i] == NULL) {
			//printf("ERROR: can't realloc in extend_size_1D_2D_int!");
			fflush(stdout);
			return;
		}
		memset(res[i], -1, sizeD2 * sizeof(int));
	}
	*in = res;

	for (int i = 0; i < newSize; i++)
	{
		for (int j = 0; j < sizeD2; j++)
		{
			//printf("in[%d][%d] = %d\n", i, j, (*in)[i][j]);
		}
	}
	//printf("extend_size_1D_2D_int end\n");
}

/*
* The set of states from which the environment can force the system to to reach a state in "to". 
*/
DdNode* control_orig(DdNode* toPrime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs, DdNode* sysTrans, DdNode* envTrans, boolean sca)
{
	DdNode* illegalSysTrans = Cudd_Not(sysTrans);
	Cudd_Ref(illegalSysTrans);

	DdNode* notSysTransOrTo = Cudd_bddOr(manager, illegalSysTrans, toPrime);
	Cudd_Ref(notSysTransOrTo);

	DdNode* notSysTransOrToStates = Cudd_bddUnivAbstract(manager, notSysTransOrTo, sysPrimeVars);
	Cudd_Ref(notSysTransOrToStates);

	DdNode* controlStates;
	if (sca) {
		// use simultaneous conjunction and abstraction
		controlStates = Cudd_bddAndAbstract(manager, envTrans, notSysTransOrToStates, envPrimeVars);
		Cudd_Ref(controlStates);
	}
	else {
		DdNode* envTransTo = Cudd_bddAnd(manager, envTrans, notSysTransOrToStates);
		Cudd_Ref(envTransTo);
		controlStates = Cudd_bddExistAbstract(manager, envTransTo, envPrimeVars);
		Cudd_Ref(controlStates);
		Cudd_RecursiveDeref(manager, envTransTo);
	}

	Cudd_RecursiveDeref(manager, toPrime);
	Cudd_RecursiveDeref(manager, illegalSysTrans);
	Cudd_RecursiveDeref(manager, notSysTransOrTo);
	Cudd_RecursiveDeref(manager, notSysTransOrToStates);

	return controlStates;
}

DdNode* control(DdNode* to, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs, DdNode* sysTrans, DdNode* envTrans, boolean sca)
{
	int n;
	unsigned int *arr;
	int varnum = Cudd_ReadSize(manager);
	arr = (unsigned int*)malloc(sizeof(unsigned int)*varnum);
	if (arr == NULL) {
		//printf("couldn't allocate array of uint of size %d\n", varnum);
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
		return control_orig(toPrime, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
	}

	DdNode* controlStates = toPrime;

	for (int i = 0; i < sys_trans_quant_list.listSize; i++) {
		DdNode* illegalSysTrans = Cudd_Not(sys_trans_quant_list.transList[i]);
		Cudd_Ref(illegalSysTrans);

		DdNode* notSysTransOrTo = Cudd_bddOr(manager, illegalSysTrans, controlStates);
		Cudd_Ref(notSysTransOrTo);		
		Cudd_RecursiveDeref(manager, illegalSysTrans);
		Cudd_RecursiveDeref(manager, controlStates);
		
		controlStates = Cudd_bddUnivAbstract(manager, notSysTransOrTo, sys_trans_quant_list.quantSets[i]);
		Cudd_Ref(controlStates);
		Cudd_RecursiveDeref(manager, notSysTransOrTo);
	}

	for (int i = 0; i < env_trans_quant_list.listSize; i++) {
		if (sca) {
			// use simultaneous conjunction and abstraction
			DdNode* tmp = controlStates;
			controlStates = Cudd_bddAndAbstract(manager, env_trans_quant_list.transList[i], tmp, env_trans_quant_list.quantSets[i]);
			Cudd_Ref(controlStates);
			Cudd_RecursiveDeref(manager, tmp);
		}
		else {
			DdNode* envTransTo = Cudd_bddAnd(manager, env_trans_quant_list.transList[i], controlStates);
			Cudd_Ref(envTransTo);
			Cudd_RecursiveDeref(manager, controlStates);
			controlStates = Cudd_bddExistAbstract(manager, envTransTo, env_trans_quant_list.quantSets[i]);
			Cudd_Ref(controlStates);
			Cudd_RecursiveDeref(manager, envTransTo);
		}
	}

	//DdNode* controlStates2 = control2(to, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
	//boolean isControlStatesEq = IS_BDD_EQ(controlStates, controlStates2);
	////printf("isYieldStatesEq = %d (true = %d, false = %d)\n", isControlStatesEq, true, false);
	//fflush(stdout);
	//Cudd_RecursiveDeref(manager, controlStates2);

	return controlStates;
}

//DdNode* control2(DdNode* to, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs, DdNode* sysTrans, DdNode* envTrans, boolean sca)
//{
//	int n;
//	unsigned int *arr;
//	int varnum = Cudd_ReadSize(manager);
//	arr = (unsigned int*)malloc(sizeof(unsigned int)*varnum);
//	if (arr == NULL) {
//		//printf("couldn't allocate array of uint of size %d\n", varnum);
//		return INVALID_BDD;
//	}
//	for (n = 0; n < varnum; ++n) {
//		DdNode* node = pairs->table[n];
//		unsigned int var = Cudd_NodeReadIndex(node);
//		arr[n] = var;
//	}
//
//	DdNode* toPrime = Cudd_bddPermute(manager, to, arr);
//	Cudd_Ref(toPrime);
//	free(arr);
//
//	DdNode* illegalSysTrans = Cudd_Not(sysTrans);
//	Cudd_Ref(illegalSysTrans);
//
//	DdNode* notSysTransOrTo = Cudd_bddOr(manager, illegalSysTrans, toPrime);
//	Cudd_Ref(notSysTransOrTo);
//	Cudd_RecursiveDeref(manager, illegalSysTrans);
//
//	DdNode* notSysTransOrToStates = Cudd_bddUnivAbstract(manager, notSysTransOrTo, sysPrimeVars);
//	Cudd_Ref(notSysTransOrToStates);
//
//	DdNode* envTransTo = Cudd_bddAnd(manager, envTrans, notSysTransOrToStates);
//	Cudd_Ref(envTransTo);
//
//	DdNode* controlStates = Cudd_bddExistAbstract(manager, envTransTo, envPrimeVars);
//	Cudd_Ref(controlStates);
//
//	////printf("use Cudd_bddAndAbstract\n");
//	//DdNode* controlStates = Cudd_bddAndAbstract(manager, envTrans, notSysTransOrToStates, envPrimeVars);
//	//Cudd_Ref(Cudd_Regular(controlStates));
//
//	Cudd_RecursiveDeref(manager, toPrime);
//	Cudd_RecursiveDeref(manager, notSysTransOrTo);
//	Cudd_RecursiveDeref(manager, notSysTransOrToStates);
//	Cudd_RecursiveDeref(manager, envTransTo);
//	return controlStates;
//}
/*
* Check whether the env player wins from some of its initial states if winEnv are its winning states
*/
boolean envWinAllInitial(DdNode* winEnv, DdNode* sysIni, DdNode* envIni,
	DdNode* sysUnprimeVars, DdNode* envUnprimeVars)
{
	DdNode* sysIniNot = Cudd_Not(sysIni);
	Cudd_Ref(Cudd_Regular(sysIniNot));

	DdNode* sysIniImpWinEnv = Cudd_bddOr(manager, sysIniNot, winEnv);
	Cudd_Ref(Cudd_Regular(sysIniImpWinEnv));
	Cudd_RecursiveDeref(manager, sysIniNot);

	DdNode* sysIniImpWinEnvForAllSys = Cudd_bddUnivAbstract(manager, sysIniImpWinEnv, sysUnprimeVars);
	Cudd_Ref(Cudd_Regular(sysIniImpWinEnvForAllSys));

	DdNode* envWinFromIniStates = Cudd_bddAnd(manager, envIni, sysIniImpWinEnvForAllSys);
	Cudd_Ref(Cudd_Regular(envWinFromIniStates));

	boolean winSomeIni = !(envWinFromIniStates == Cudd_Not(Cudd_ReadOne(manager)));
	////printf("winSomeIni = %d\n", winSomeIni);

	Cudd_RecursiveDeref(manager, sysIniImpWinEnv);
	Cudd_RecursiveDeref(manager, sysIniImpWinEnvForAllSys);
	Cudd_RecursiveDeref(manager, envWinFromIniStates);

	return winSomeIni;
}

void copy_to_rabin_mem_sizeD3(int ** cx_mem)
{
	rabin_mem.sizeD3 = malloc(rabin_mem.sizeD1 * sizeof(int*));

	for (int i = 0; i < rabin_mem.sizeD1; i++)
	{
		rabin_mem.sizeD3[i] = malloc(rabin_mem.xSizeD2 * sizeof(int));
		for (int j = 0; j < rabin_mem.xSizeD2; j++)
		{
			rabin_mem.sizeD3[i][j] = cx_mem[i][j];
			////printf("rabin_mem.sizeD3[%d][%d] = %d\n", i, j, rabin_mem.sizeD3[i][j]);  fflush(stdout);
		}
	}
}

void copy_to_rabin_mem(inc_rabin_data inc_data, int ** cx_mem, int x_currSize, int sizeD1)
{
	for (int k = 0; k < sizeD1; k++)
	{
		rabin_mem.z_mem[k] = inc_data.z_mem[k];
		Cudd_Ref(Cudd_Regular(rabin_mem.z_mem[k]));

		for (int i = 0; i < inc_data.sizeD2; i++)
		{
			// NOTE: cx_mem should be allocated at least as the num of sys justices times env justices
			cx_mem[k][i] = inc_data.sizeD3[k][i];
			if (x_currSize <= inc_data.sizeD3[k][i])
			{
				rabin_mem.x_mem[k][i] = realloc(rabin_mem.x_mem[k][i], inc_data.sizeD3[k][i] * sizeof(DdNode*));
				if (rabin_mem.x_mem[k][i] == NULL) {
					//printf("ERROR: can't realloc in rabin_mem.x_mem[%d][%d]!\n", k, i);
					fflush(stdout);
					return;
				}
			}
			for (int cx = 0; cx < inc_data.sizeD3[k][i]; cx++)
			{
				rabin_mem.x_mem[k][i][cx] = inc_data.x_mem[k][i][cx];
				Cudd_Ref(Cudd_Regular(rabin_mem.x_mem[k][i][cx]));
			}
		}

	}
}

//void handle_inc_guar_added_r(inc_rabin_data inc_data, DdNode** z)
//{
//	if (IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_NEW_JUSTICE_ADDED)
//		|| IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_NEW_SAFETY_ADDED))
//	{
//		int lastIdx = inc_data.sizeD1 - 1;
//		FREE_BDD(*z);
//		*z = inc_data.z_mem[lastIdx];
//		Cudd_Ref(Cudd_Regular(*z));
//		//printf("use inc_data.z_mem[%d] for current Z, is Zero = %d\n", lastIdx, (*z == Cudd_Not(Cudd_ReadOne(manager))));
//	}
//}

void handle_inc_guar_added_r(inc_rabin_data inc_data, int sysJSize, int * j_start_idx, DdNode** z, int ** cx_mem, int x_currSize, int* cz)
{
	if (IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_NEW_JUSTICE_ADDED)
		&& !IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_NEW_SAFETY_ADDED)
		&& (inc_data.least_removed_justice > 0))
	{
		//printf("New justice(s) was added, to an existing list of justices. Current num of sys justices is %d\n", sysJSize);
		*j_start_idx = inc_data.least_removed_justice; // NOTE: the new justice idx - "least added", not removed.
		*cz = inc_data.sizeD1;
		//printf("New justice was added, starting from j_start_idx = %d\n", *j_start_idx);
		////printf("x_currSize = %d, inc_data.sizeD1 = %d, inc_data.sizeD2 = %d, cz = %d\n", x_currSize, inc_data.sizeD1, inc_data.sizeD2, *cz); fflush(stdout);
		copy_to_rabin_mem(inc_data, cx_mem, x_currSize, inc_data.sizeD1);
		
		FREE_BDD(*z);
		*z = inc_data.z_mem[inc_data.sizeD1 - 1];
		Cudd_Ref(Cudd_Regular(*z));

		//printf("New justice was added, starting from z is one = %d\n", (z == Cudd_ReadOne(manager)));
	}
	else if (IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_NEW_JUSTICE_ADDED)
		|| IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_NEW_SAFETY_ADDED))
	{
		//printf("use inc_data.start_z\n");
		FREE_BDD(*z);
		*z = inc_data.start_z;
		Cudd_Ref(Cudd_Regular(*z));
	}

	//printf("is starting Z from Zero = %d\n", (z == Cudd_Not(Cudd_ReadOne(manager))));
}
void handle_inc_safety_removed_r(inc_rabin_data inc_data, DdNode** y)
{
	if (IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_PREV_SAFETY_REMOVED)) 
	{
		int lastIdx = inc_data.sizeD1 - 1;
		FREE_BDD(*y);
		*y = inc_data.z_mem[lastIdx];
		Cudd_Ref(Cudd_Regular(*y));
		//printf("use inc_data.z_mem[%d] for current Y, is One = %d\n", lastIdx, (*y == Cudd_ReadOne(manager)));
	}
}

void handle_inc_only_j_removed_r(inc_rabin_data inc_data, int * j_start_idx, DdNode** z, int ** cx_mem, int x_currSize, int* cz)
{
	if (!IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_PREV_SAFETY_REMOVED)
		&& IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_PREV_JUSTICE_REMOVED)
		&& inc_data.least_removed_justice > 0)
	{
		//printf("previous justice was removed, inc_data.least_removed_justice = %d\n", inc_data.least_removed_justice);
		// NOTE: copies the memory of the first iteration over sys justices
		*cz = inc_data.least_removed_justice;
		copy_to_rabin_mem(inc_data, cx_mem, x_currSize, inc_data.least_removed_justice);
		for (int k = 0; k < inc_data.least_removed_justice; k++)
		{
			rabin_mem.z_mem[k] = inc_data.z_mem[k];
			Cudd_Ref(Cudd_Regular(rabin_mem.z_mem[k]));

			for (int i = 0; i < inc_data.sizeD2; i++)
			{
				// NOTE: cx_mem should be allocated at least as the num of sys justices times env justices
				cx_mem[k][i] = inc_data.sizeD3[k][i];
				if (x_currSize <= inc_data.sizeD3[k][i])
				{
					rabin_mem.x_mem[k][i] = realloc(rabin_mem.x_mem[k][i], inc_data.sizeD3[k][i] * sizeof(DdNode*));
					if (rabin_mem.x_mem[k][i] == NULL) {
						//printf("ERROR: can't realloc in rabin_mem.x_mem[%d][%d]!\n", k, i);
						fflush(stdout);
						return;
					}
				}
				for (int cx = 0; cx < inc_data.sizeD3[k][i]; cx++)
				{
					rabin_mem.x_mem[k][i][cx] = inc_data.x_mem[k][i][cx];
					Cudd_Ref(Cudd_Regular(rabin_mem.x_mem[k][i][cx]));
				}
			}
		}
		FREE_BDD(*z);
		*z = rabin_mem.z_mem[inc_data.least_removed_justice - 1];
		Cudd_Ref(Cudd_Regular(*z));
		*j_start_idx = inc_data.least_removed_justice;
		//printf("starting first z iteration from j_start_idx = %d\n", *j_start_idx);
	}
}

boolean rabin_game(DdNode** sysJ, int sysJSize, DdNode** envJ, int envJSize, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysUnprime, DdNode* envUnprime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	boolean efp, boolean eun, boolean fpr, boolean sca)
{
	inc_rabin_data inc_data;
	return rabin_game_inc(sysJ, sysJSize, envJ, envJSize, sysIni, envIni, sysTrans, envTrans,
		sysUnprime, envUnprime, sysPrimeVars, envPrimeVars, pairs, efp, eun, fpr, sca, false, inc_data);
}

boolean rabin_game_inc(DdNode** sysJ, int sysJSize, DdNode** envJ, int envJSize, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysUnprime, DdNode* envUnprime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	boolean efp, boolean eun, boolean fpr, boolean sca, boolean isInc, inc_rabin_data inc_data)
{
	//printf("\n----Start Rabin Game: efp=%d, eun=%d, fpr=%d----\n", efp, eun, fpr);
	if (isInc) print_inc_type(inc_data.type_bitmap);

	rabin_mem.xSizeD2 = envJSize;

	int currSizeZ = 20 * sysJSize;
	if (isInc && is_inc_only_ini(inc_data.type_bitmap)) { currSizeZ = inc_data.sizeD1; }
	
	//rabin_mem.z_mem = malloc(currSizeZ * sizeof(DdNode**));
	rabin_mem.z_mem = malloc(currSizeZ * sizeof(DdNode*));

	rabin_mem.x_mem = malloc(currSizeZ * sizeof(DdNode***));
	int ** cx_mem = malloc(currSizeZ * sizeof(int*));

	int currSizeX = 50;
	for (int i = 0; i < currSizeZ; i++)
	{	
		//rabin_mem.z_mem[i] = malloc(sysJSize * sizeof(DdNode*));
		rabin_mem.x_mem[i] = malloc(envJSize * sizeof(DdNode**));
		cx_mem[i] = malloc(envJSize * sizeof(int));
		memset(cx_mem[i], -1, envJSize * sizeof(int));
		for (int envJi = 0; envJi < envJSize; envJi++)
		{
			rabin_mem.x_mem[i][envJi] = malloc(currSizeX * sizeof(DdNode*));
		}
	}

	if (isInc && is_inc_only_ini(inc_data.type_bitmap))
	{
		//printf("Only ini states changed\n");
		boolean env_win = envWinAllInitial(inc_data.z_mem[inc_data.sizeD1 - 1], sysIni, envIni, sysUnprime, envUnprime);
		copy_to_rabin_mem(inc_data, cx_mem, currSizeX, inc_data.sizeD1);
		rabin_mem.sizeD1 = inc_data.sizeD1;
		rabin_mem.xSizeD2 = inc_data.sizeD2;
		copy_to_rabin_mem_sizeD3(cx_mem);
		//printf("End Rabin Game: is env winning = %d\n", env_win);
		return env_win;
	}
	// NOTE: additional memory for X fixed point recycle
	int currSizeY = 50;
	int * cy_mem;
	if (fpr) {
		//printf("alloc x_mem_recycle\n");
		rabin_mem.x_mem_recycle = malloc(sysJSize * sizeof(DdNode***));
		int tmp = 0;
		cy_mem = malloc(sysJSize * sizeof(int));
		memset(cy_mem, -1, sysJSize * sizeof(int));
		for (int j = 0; j < sysJSize; j++)
		{
			rabin_mem.x_mem_recycle[j] = malloc(envJSize * sizeof(DdNode**));
			for (int i = 0; i < envJSize; i++)
			{
				rabin_mem.x_mem_recycle[j][i] = malloc(currSizeY * sizeof(DdNode*));
			}
		}
		//printf("after alloc x_mem_recycle\n");
	}
	else {
		rabin_mem.x_mem_recycle = NULL;
		cy_mem = NULL;
	}

	//for (int i = 0; i < currSizeZ; i++)
	//{
	//	for (int j = 0; j < envJSize; j++)
	//	{
	//		//printf("cx_mem[%d][%d] = %d\n", i, j, cx_mem[i][j]);  fflush(stdout);
	//	}
	//}

	int cx = 0; // count x
	int cy = 0; // count y - only foe X fpr
	int cz = 0; // count z

	DdNode *x = NULL, *y = NULL, *z = NULL;
	DdNode *xPrev, *yPrev, *zPrev;
	boolean firstZIter = true;
	
	z = Cudd_Not(Cudd_ReadOne(manager));
	Cudd_Ref(z);
	zPrev = NULL;
	yPrev = NULL;
	xPrev = NULL;
	int j_start_idx = 0;

	if (isInc) handle_inc_guar_added_r(inc_data, sysJSize, &j_start_idx, &z, cx_mem, currSizeX, &cz);

	int zIters = 0;
	int yIters = 0;
	int xIters = 0;

	int xtmp = 0;
	int ytmp = 0;

	boolean isFinished = false;

	while (zPrev == NULL || !IS_BDD_EQ(z, zPrev))
	{
		zIters++;

		//if (zPrev == NULL) //printf("zPrev is NULL\n");
		//if (zPrev != NULL) //printf("IS_BDD_EQ(z, zPrev) = %d\n", IS_BDD_EQ(z, zPrev)); 

		FREE_BDD(zPrev);
		zPrev = z;
		Cudd_Ref(zPrev);

		if (isInc && firstZIter) handle_inc_only_j_removed_r(inc_data, &j_start_idx, &z, cx_mem, currSizeX, &cz);

		for (int j = j_start_idx; j < sysJSize; j++)
		{
			//printf("Z loop %d: j = %d\n", zIters, j);
			//fflush(stdout);
			//Cudd_DebugCheck(manager);
			//Cudd_CheckKeys(manager);

			cy = 0;
			FREE_BDD(y);
			y = Cudd_ReadOne(manager);
			Cudd_Ref(y);

			if (isInc) handle_inc_safety_removed_r(inc_data, &y);

			FREE_BDD(yPrev);

			DdNode* controlStatesZ = control(z, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
			DdNode* notSysJ = Cudd_Not(sysJ[j]);
			Cudd_Ref(notSysJ);

			//Second - Y fixed point 
			while (yPrev == NULL || !IS_BDD_EQ(y, yPrev))
			{
				yIters++;
				ytmp++;
				////printf("y iterations = %d\, isFalse = %d \n", ytmp, y == Cudd_Not(Cudd_ReadOne(manager))); fflush(stdout);
				//Cudd_DebugCheck(manager);
				//Cudd_CheckKeys(manager);

				FREE_BDD(yPrev);
				yPrev = y;
				Cudd_Ref(yPrev);
				DdNode* controlStatesY = control(y, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
				DdNode* nextYAndNotJj = Cudd_bddAnd(manager, controlStatesY, notSysJ);
				Cudd_Ref(nextYAndNotJj);
				FREE_BDD(controlStatesY);
				
				FREE_BDD(y);
				y = Cudd_ReadOne(manager);
				Cudd_Ref(y);

				for (int i = 0; i < envJSize; i++)
				{
					////printf("Y loop - i = %d\n", i); fflush(stdout);
					//Cudd_PrintDebug(manager, y, 2, 1);
					//Cudd_CheckKeys(manager);
					//Cudd_DebugCheck(manager);

					DdNode* nextYAndNotJjAndNotJi = Cudd_bddAnd(manager, envJ[i], nextYAndNotJj);
					Cudd_Ref(nextYAndNotJjAndNotJi);

					DdNode* pre = Cudd_bddOr(manager, controlStatesZ, nextYAndNotJjAndNotJi);
					Cudd_Ref(pre);

					FREE_BDD(nextYAndNotJjAndNotJi);
					FREE_BDD(x);

					if (fpr && !firstZIter)
					{
						//int rcy = cy;
						//if (cy_mem[j] <= cy)
						//{
						//	rcy = cy_mem[j] - 1;
						//}
						//x = Cudd_bddOr(manager, rabin_mem.x_mem_recycle[j][i][rcy], pre);
						
						int rcy = -1;
						if (cy < cy_mem[j])
						{
							rcy = cy;
						}
						
						if (rcy == -1) {
							x = Cudd_Not(Cudd_ReadOne(manager));
						}
						else {
							//printf("recycleFixPoint X for j=%d, i=%d, rcy=%d\n", j, i, rcy);
							x = Cudd_bddOr(manager, rabin_mem.x_mem_recycle[j][i][rcy], pre);
						}
						
						//int prev_zItr = cz - sysJSize;
						//int prev_zItr_cx = cx_mem[prev_zItr][i];
						////printf("recycleFixPoint X for prev_zItr=%d, i=%d, prev_zItr_cx=%d\n", prev_zItr, i, prev_zItr_cx);
						//x = rabin_mem.x_mem[prev_zItr][i][prev_zItr_cx - 1];
						////x = Cudd_bddOr(manager, rabin_mem.x_mem[prev_zItr][i][prev_zItr_cx-1], pre);
					}
					else {
						x = Cudd_Not(Cudd_ReadOne(manager));
					}

					Cudd_Ref(x);
					cx = 0;

					//Cudd_DebugCheck(manager);
					////printf("X loop before\n"); fflush(stdout);

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
						Cudd_Ref(xPrev);
											
						DdNode* controlStatesX = control(x, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
						DdNode* ctrlStatesXAndNotJ = Cudd_bddAnd(manager, controlStatesX, notSysJ);
						Cudd_Ref(ctrlStatesXAndNotJ);
						FREE_BDD(controlStatesX);

						FREE_BDD(x);
						x = Cudd_bddOr(manager, ctrlStatesXAndNotJ, pre);
						Cudd_Ref(x);
						FREE_BDD(ctrlStatesXAndNotJ);

						////printf("cx_mem[%d][%d] = %d , cx = %d\n", cz, i, cx_mem[cz][i], cx); fflush(stdout);

						if (cx < cx_mem[cz][i]) {
							FREE_BDD(rabin_mem.x_mem[cz][i][cx]);
						}

						rabin_mem.x_mem[cz][i][cx] = x;
						Cudd_Ref(rabin_mem.x_mem[cz][i][cx]);						
						cx++;
						// extend size of x_mem
						if (cx == currSizeX) {
							currSizeX = currSizeX * 2;
							extend_size_3D(rabin_mem.x_mem, currSizeZ, envJSize, currSizeX);
						}

					} // End X fixed point
					
					////printf("j = %d, i = %d, cx = %d\n", j,i,cx); fflush(stdout);
					////printf("cx = %d, cx_mem[%d][%d] = %d\n", cx, cz, i, cx_mem[cz][i]); fflush(stdout);

					cx_mem[cz][i] = cx;

					if (fpr) {
						//if (x_recycle[j][i].size() > cy) {
						//	x_recycle[j][i].get(cy).free();
						//}
						//else {
						//	// extend vector
						//	x_recycle[j][i].setSize(cy + 1);
						//}
						//// store fixed-point x for current y iteration
						//x_recycle[j][i].set(cy, x.id());
						////printf("update rabin_mem.x_mem_recycle[%d][%d][%d]\n", j,i,cy); fflush(stdout);
						////printf("cy_mem[%d] = %d\n", j, cy_mem[j]); fflush(stdout);
						if (cy < cy_mem[j])
						{
							////printf("cy (%d) < cy_mem[%d]\n", cy, cy_mem[j]); fflush(stdout);
							FREE_BDD(rabin_mem.x_mem_recycle[j][i][cy]);
						}
						rabin_mem.x_mem_recycle[j][i][cy] = x;
						Cudd_Ref(rabin_mem.x_mem_recycle[j][i][cy]);
					}

					FREE_BDD(xPrev);
					FREE_BDD(pre);

					DdNode* tmp = Cudd_bddAnd(manager, y, x);
					Cudd_Ref(tmp);
					FREE_BDD(y);
					y = tmp;
				} // End loop over envJ

				FREE_BDD(nextYAndNotJj);

				cy++;
				if (fpr && (cy == currSizeY)) {
					currSizeY = currSizeY * 2;
					//printf("extend size of 3D of rabin_mem.x_mem_recycle to %d\n", currSizeY);
					extend_size_3D(rabin_mem.x_mem_recycle, sysJSize, envJSize, currSizeY);
				}

				////printf("IS_BDD_EQ(y, yPrev) = %d\n", IS_BDD_EQ(y, yPrev));
			} // End Y fixed point
			
			ytmp = 0;

			FREE_BDD(controlStatesZ);
			FREE_BDD(notSysJ);

			if (fpr) {
				cy_mem[j] = cy;
			}

			DdNode* tmp = Cudd_bddOr(manager, z, y);
			Cudd_Ref(tmp);
			FREE_BDD(z);
			FREE_BDD(y);
			z = tmp;

			rabin_mem.z_mem[cz] = z;
			Cudd_Ref(rabin_mem.z_mem[cz]);
			cz++;

			if (efp && !firstZIter) {
				////printf("firstZIter = %d\n", firstZIter);
				if (IS_BDD_EQ(rabin_mem.z_mem[cz-1-sysJSize], z)) {
					//printf("detected early fixed point\n");
					isFinished = true;
					break;
				}
			}

			if (eun && envWinAllInitial(z, sysIni, envIni, sysUnprime, envUnprime)) {
				//printf("envWinAllInitial is true - env wins from some initial states\n");
				isFinished = true;
				break;
			}

			////printf("currSizeZ = %d, cz = %d\n", currSizeZ, cz); fflush(stdout);

			if (cz == currSizeZ) {
				int prevSizeZ = currSizeZ;
				currSizeZ = currSizeZ * 2;
				extend_size_1D(&(rabin_mem.z_mem), prevSizeZ, currSizeZ);
				extend_size_1D_3D(&(rabin_mem.x_mem), envJSize, currSizeX, prevSizeZ, currSizeZ);
				extend_size_1D_2D_int(&cx_mem, envJSize, prevSizeZ, currSizeZ);
			}

			if (isFinished) break;
		} // End loop over sysJ

		j_start_idx = 0;
		firstZIter = false;
		if (isFinished) break;

	} // End Z fixed point
	FREE_BDD(zPrev);
	FREE_BDD(x);

	//for (int i = 0; i < currSizeZ; i++)
	//{
	//	for (int j = 0; j < envJSize; j++)
	//	{
	//		//printf("cx_mem[%d][%d] = %d\n", i, j, cx_mem[i][j]);  fflush(stdout);
	//	}
	//}

	rabin_mem.sizeD1 = cz;
	copy_to_rabin_mem_sizeD3(cx_mem);
	//rabin_mem.sizeD3 = malloc(cz * sizeof(int*));
	//for (int i = 0; i < cz; i++)
	//{
	//	rabin_mem.sizeD3[i] = malloc(envJSize * sizeof(int));
	//	for (int j = 0; j < envJSize; j++)
	//	{
	//		rabin_mem.sizeD3[i][j] = cx_mem[i][j];
	//		////printf("rabin_mem.sizeD3[%d][%d] = %d\n", i, j, rabin_mem.sizeD3[i][j]);  fflush(stdout);
	//	}
	//}

	// NOTE: free the additional memory for X fixed point recycle
	if (fpr) {
		for (int sysJi = 0; sysJi < sysJSize; sysJi++)
		{
			for (int envJi = 0; envJi < envJSize; envJi++)
			{
				for (int i = 0; i < cy_mem[sysJi]; i++)
				{
					FREE_BDD(rabin_mem.x_mem_recycle[sysJi][envJi][i]);
				}
				free(rabin_mem.x_mem_recycle[sysJi][envJi]);
			}
			free(rabin_mem.x_mem_recycle[sysJi]);
		}
		free(rabin_mem.x_mem_recycle);
		rabin_mem.x_mem_recycle = NULL;
		free(cy_mem);
		cy_mem = NULL;
	}

	//printf("z iterations = %d\n", zIters);
	//printf("y iterations = %d\n", yIters);
	//printf("x iterations = %d\n", xIters);

	boolean env_win = envWinAllInitial(z, sysIni, envIni, sysUnprime, envUnprime);
	//printf("End Rabin Game: is env winning = %d\n", env_win);

	//Cudd_DebugCheck(manager);
	//Cudd_CheckKeys(manager);
	//fflush(stdout);

	return env_win;
}


