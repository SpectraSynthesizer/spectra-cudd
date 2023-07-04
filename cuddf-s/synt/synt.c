/*
*	Implementation of the general functions from synt.h
*/

#include "synt.h"

#include <time.h> 

sizeD1 = 0;
sizeD2 = 0;



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

void handle_inc_guar_added(inc_gr1_data inc_data, int sysJSize, int* j_start_idx, DdNode** z, int currSize, int* cy_mem)
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
	}
	else if (IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_NEW_JUSTICE_ADDED)
		|| IS_BIT_ON(inc_data.type_bitmap, INC_TYPE_NEW_SAFETY_ADDED))
	{
		//printf("use inc_data.start_z\n");
		*z = inc_data.start_z;
		Cudd_Ref(Cudd_Regular(*z));
	}

	//printf("is starting Z from One = %d\n", (z == Cudd_ReadOne(manager)));
}

void handle_inc_only_j_removed(inc_gr1_data inc_data, int* j_start_idx, DdNode** z, int x_currSize, int* cy_mem)
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




void createUtilVar(int size, int* from, int* to) {

	int level = 0;
	int until;
	while (size > 0) {
		until = Cudd_bddNewVarAtLevel(manager, level)->index;
		size /= 2;
		++level;
	}
	*to = until;
	*from = until - level + 1;
}

DdNode* ithVarInteger(DdManager* manager, int* vars, int varNum, int value) {

	DdNode* tmp;
	DdNode* curr;
	DdNode* res = Cudd_ReadOne(manager);
	Cudd_Ref(res);
	for (int i = 0; i < varNum; i++) {
		if (value % 2 == 0) {
			curr = Cudd_Not(Cudd_bddIthVar(manager, vars[i]));
		} else {
			curr = Cudd_bddIthVar(manager, vars[i]);
		}
		
		tmp = Cudd_bddAnd(manager, curr, res);
		Cudd_Ref(tmp);
		FREE_BDD(res);
		res = tmp;
		value /= 2;
	}
	return res;
}


// GR(1)* functions

DdNode* getFulfillBDD(DdManager* manager, int* exjindices, int exjindicesSize, int* findices, int findicesSize) {

	DdNode *currExJ, *currF, *tmp1, *tmp2, *currJustice;
	DdNode* fulfill_ret = Cudd_ReadOne(manager);
	Cudd_Ref(fulfill_ret);

	for (int exj = 0; exj < gr1_star_mem.exist_sizeD1; exj++) {

		currJustice = Cudd_ReadOne(manager);
		Cudd_Ref(currJustice);
		for (int f = 0; f < gr1_star_mem.fulfill_exist_sizeD2[exj]; f++) {

			currExJ = ithVarInteger(manager, exjindices, exjindicesSize, exj);
			currF = ithVarInteger(manager, findices, findicesSize, f);

			tmp1 = Cudd_bddAnd(manager, currExJ, currF);
			Cudd_Ref(tmp1);
			tmp2 = Cudd_bddIte(manager,
				tmp1,
				gr1_star_mem.fulfill_exist_mem[exj][f],
				Cudd_ReadOne(manager)
			);
			Cudd_Ref(tmp2);
			FREE_BDD(tmp1);

			FREE_BDD(currExJ);
			FREE_BDD(currF);

			tmp1 = Cudd_bddAnd(manager, currJustice, tmp2);
			Cudd_Ref(tmp1);
			FREE_BDD(currJustice);
			FREE_BDD(tmp2);
			currJustice = tmp1;
		}

		tmp1 = Cudd_bddAnd(manager, fulfill_ret, currJustice);
		Cudd_Ref(tmp1);
		FREE_BDD(currJustice);
		FREE_BDD(fulfill_ret);
		fulfill_ret = tmp1;
	}

	return fulfill_ret;
}

DdNode* getTowardsBDD(DdManager* manager, int* exjindices, int exjindicesSize, int* tindices, int tindicesSize) {

	DdNode *currExJ, *currT, *tmp1, *tmp2, *currJustice;
	DdNode* towards_ret = Cudd_ReadOne(manager);
	Cudd_Ref(towards_ret);

	for (int exj = 0; exj < gr1_star_mem.exist_sizeD1; exj++) {

		currJustice = Cudd_ReadOne(manager);
		Cudd_Ref(currJustice);
		for (int t = 0; t < gr1_star_mem.towards_exist_sizeD2[exj]; t++) {

			currExJ = ithVarInteger(manager, exjindices, exjindicesSize, exj);
			currT = ithVarInteger(manager, tindices, tindicesSize, t);

			tmp1 = Cudd_bddAnd(manager, currExJ, currT);
			Cudd_Ref(tmp1);
			tmp2 = Cudd_bddIte(manager,
				tmp1,
				gr1_star_mem.towards_exist_mem[exj][t],
				Cudd_ReadOne(manager)
			);
			Cudd_Ref(tmp2);
			FREE_BDD(tmp1);

			FREE_BDD(currExJ);
			FREE_BDD(currT);

			tmp1 = Cudd_bddAnd(manager, currJustice, tmp2);
			Cudd_Ref(tmp1);
			FREE_BDD(currJustice);
			FREE_BDD(tmp2);
			currJustice = tmp1;
		}

		tmp1 = Cudd_bddAnd(manager, towards_ret, currJustice);
		Cudd_Ref(tmp1);
		FREE_BDD(currJustice);
		FREE_BDD(towards_ret);
		towards_ret = tmp1;
	}

	return towards_ret;
}

DdNode* getEnvViolationBDD(DdManager* manager, int* iindices, int iindicesSize, int* kindices, int kindicesSize) {

	DdNode *currI, *currK, *tmp1, *tmp2, *currLevel;
	DdNode* env_violation_ret = Cudd_ReadOne(manager);
	Cudd_Ref(env_violation_ret);

	for (int i = 0; i < gr1_mem.sizeD2; i++) {

		currLevel = Cudd_ReadOne(manager);
		Cudd_Ref(currLevel);
		for (int k = 0; k < gr1_star_mem.envJ_violation_sizeD2; k++) {

			currI = ithVarInteger(manager, iindices, iindicesSize, i);
			currK = ithVarInteger(manager, kindices, kindicesSize, k);

			tmp1 = Cudd_bddAnd(manager, currI, currK);
			Cudd_Ref(tmp1);
			tmp2 = Cudd_bddIte(manager,
				tmp1,
				gr1_star_mem.envJ_violation_mem[i][k],
				Cudd_ReadOne(manager)
			);
			Cudd_Ref(tmp2);
			FREE_BDD(tmp1);

			FREE_BDD(currI);
			FREE_BDD(currK);

			tmp1 = Cudd_bddAnd(manager, currLevel, tmp2);
			Cudd_Ref(tmp1);
			FREE_BDD(currLevel);
			FREE_BDD(tmp2);
			currLevel = tmp1;
		}

		tmp1 = Cudd_bddAnd(manager, env_violation_ret, currLevel);
		Cudd_Ref(tmp1);
		FREE_BDD(currLevel);
		FREE_BDD(env_violation_ret);
		env_violation_ret = tmp1;
	}

	return env_violation_ret;
}

DdNode* getFixpointsStarBDD(DdManager* manager, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int* kindices, int kindicesSize) {

	DdNode *currI, *currJ, *currK, *tmp1, *tmp2, *currLevel, *currJustice;
	DdNode* fixpoints_ret = Cudd_ReadOne(manager);
	Cudd_Ref(fixpoints_ret);

	for (int j = 0; j < gr1_star_mem.x_y_z_sizeD1; j++) {

		currJustice = Cudd_ReadOne(manager);
		Cudd_Ref(currJustice);
		for (int k = 0; k < gr1_star_mem.x_sizeD3[j]; k++) {

			currLevel = Cudd_ReadOne(manager);
			Cudd_Ref(currLevel);
			for (int i = 0; i < gr1_star_mem.x_sizeD2; i++) {

				currJ = ithVarInteger(manager, jindices, jindicesSize, j);
				currK = ithVarInteger(manager, kindices, kindicesSize, k);
				currI = ithVarInteger(manager, iindices, iindicesSize, i);

				tmp1 = Cudd_bddAnd(manager, currJ, currK);
				Cudd_Ref(tmp1);
				tmp2 = Cudd_bddAnd(manager, tmp1, currI);
				Cudd_Ref(tmp2);
				FREE_BDD(tmp1);
				tmp1 = Cudd_bddIte(manager,
					tmp2,
					gr1_star_mem.x_mem[j][i][k],
					Cudd_ReadOne(manager)
				);
				Cudd_Ref(tmp1);
				FREE_BDD(tmp2);

				tmp2 = Cudd_bddAnd(manager, currLevel, tmp1);
				Cudd_Ref(tmp2);
				FREE_BDD(tmp1);
				currLevel = tmp2;

				FREE_BDD(currI);
				FREE_BDD(currJ);
				FREE_BDD(currK);
			}

			tmp1 = Cudd_bddAnd(manager, currJustice, currLevel);
			Cudd_Ref(tmp1);
			FREE_BDD(currLevel);
			FREE_BDD(currJustice);
			currJustice = tmp1;
		}

		tmp1 = Cudd_bddAnd(manager, fixpoints_ret, currJustice);
		Cudd_Ref(tmp1);
		FREE_BDD(currJustice);
		FREE_BDD(fixpoints_ret);
		fixpoints_ret = tmp1;
	}

	return fixpoints_ret;
}

DdNode* getJusticesStarBDD(DdManager* manager, DdNode** sysJ, DdNode** envJ, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int utilindex) {

	DdNode *currI, *currJ, *tmp1, *tmp2;
	DdNode* justices_ret = Cudd_ReadOne(manager);
	Cudd_Ref(justices_ret);

	DdNode* util0 = Cudd_Not(Cudd_bddIthVar(manager, utilindex));

	for (int j = 0; j < gr1_star_mem.x_y_z_sizeD1; j++) {

		currJ = ithVarInteger(manager, jindices, jindicesSize, j);
		tmp1 = Cudd_bddAnd(manager, util0, currJ);
		Cudd_Ref(tmp1);
		tmp2 = Cudd_bddIte(manager,
			tmp1,
			sysJ[j],
			Cudd_ReadOne(manager)
		);
		Cudd_Ref(tmp2);
		FREE_BDD(tmp1);

		tmp1 = Cudd_bddAnd(manager, justices_ret, tmp2);
		Cudd_Ref(tmp1);
		FREE_BDD(tmp2);
		justices_ret = tmp1;

		FREE_BDD(currJ);
	}

	DdNode* util1 = Cudd_bddIthVar(manager, utilindex);

	for (int i = 0; i < gr1_star_mem.x_sizeD2; i++) {

		currI = ithVarInteger(manager, iindices, iindicesSize, i);
		tmp1 = Cudd_bddAnd(manager, util1, currI);
		Cudd_Ref(tmp1);
		tmp2 = Cudd_bddIte(manager,
			tmp1,
			envJ[i],
			Cudd_ReadOne(manager)
		);
		Cudd_Ref(tmp2);
		FREE_BDD(tmp1);

		tmp1 = Cudd_bddAnd(manager, justices_ret, tmp2);
		Cudd_Ref(tmp1);
		FREE_BDD(tmp2);
		justices_ret = tmp1;

		FREE_BDD(currI);
	}

	FREE_BDD(util0);
	FREE_BDD(util1);

	return justices_ret;
}





// GR(1) functions!!!

DdNode* getJusticesBDD(DdManager* manager, DdNode** sysJ, DdNode** envJ, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int utilindex) {

	DdNode *currI, *currJ, *tmp1, *tmp2;
	DdNode* justices_ret = Cudd_ReadOne(manager);
	Cudd_Ref(justices_ret);

	DdNode* util0 = Cudd_Not(Cudd_bddIthVar(manager, utilindex));

	for (int j = 0; j < gr1_mem.sizeD1; j++) {

		currJ = ithVarInteger(manager, jindices, jindicesSize, j);
		tmp1 = Cudd_bddAnd(manager, util0, currJ);
		Cudd_Ref(tmp1);
		tmp2 = Cudd_bddIte(manager,
			tmp1,
			sysJ[j],
			Cudd_ReadOne(manager)
		);
		Cudd_Ref(tmp2);
		FREE_BDD(tmp1);

		tmp1 = Cudd_bddAnd(manager, justices_ret, tmp2);
		Cudd_Ref(tmp1);
		FREE_BDD(tmp2);
		justices_ret = tmp1;

		FREE_BDD(currJ);
	}

	DdNode* util1 = Cudd_bddIthVar(manager, utilindex);

	for (int i = 0; i < gr1_mem.sizeD2; i++) {

		currI = ithVarInteger(manager, iindices, iindicesSize, i);
		tmp1 = Cudd_bddAnd(manager, util1, currI);
		Cudd_Ref(tmp1);
		tmp2 = Cudd_bddIte(manager,
			tmp1,
			envJ[i],
			Cudd_ReadOne(manager)
		);
		Cudd_Ref(tmp2);
		FREE_BDD(tmp1);

		tmp1 = Cudd_bddAnd(manager, justices_ret, tmp2);
		Cudd_Ref(tmp1);
		FREE_BDD(tmp2);
		justices_ret = tmp1;

		FREE_BDD(currI);
	}

	FREE_BDD(util0);
	FREE_BDD(util1);

	return justices_ret;
}

DdNode* getTransBDD(DdManager* manager, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans, 
	int* jindices, int jindicesSize, int* iindices, int iindicesSize, int utilindex) {

	DdNode *tmp1, *tmp2;
	DdNode* trans_ret = Cudd_ReadOne(manager);
	Cudd_Ref(trans_ret);

	DdNode* util0 = Cudd_Not(Cudd_bddIthVar(manager, utilindex));
	DdNode* jn0 = ithVarInteger(manager, jindices, jindicesSize, 0);
	DdNode* in0 = ithVarInteger(manager, iindices, iindicesSize, 0);
	DdNode* util1 = Cudd_bddIthVar(manager, utilindex);
	DdNode* jn1 = ithVarInteger(manager, jindices, jindicesSize, 1);
	DdNode* in1 = ithVarInteger(manager, iindices, iindicesSize, 1);


	// Add sysIni

	tmp1 = Cudd_bddAnd(manager, util0, jn0);
	Cudd_Ref(tmp1);
	tmp2 = Cudd_bddIte(manager,
		tmp1,
		sysIni,
		Cudd_ReadOne(manager)
	);
	Cudd_Ref(tmp2);
	FREE_BDD(tmp1);

	tmp1 = Cudd_bddAnd(manager, trans_ret, tmp2);
	Cudd_Ref(tmp1);
	FREE_BDD(tmp2);
	trans_ret = tmp1;


	// Add sysTrans

	tmp2 = Cudd_bddAnd(manager, util0, jn1);
	Cudd_Ref(tmp2);
	tmp1 = Cudd_bddIte(manager,
		tmp2,
		sysTrans,
		Cudd_ReadOne(manager)
	);
	Cudd_Ref(tmp1);
	FREE_BDD(tmp2);

	tmp2 = Cudd_bddAnd(manager, trans_ret, tmp1);
	Cudd_Ref(tmp2);
	FREE_BDD(tmp1);
	trans_ret = tmp2;


	// Add envIni
	
	tmp1 = Cudd_bddAnd(manager, util1, in0);
	Cudd_Ref(tmp1);
	tmp2 = Cudd_bddIte(manager,
		tmp1,
		envIni,
		Cudd_ReadOne(manager)
	);
	Cudd_Ref(tmp2);
	FREE_BDD(tmp1);

	tmp1 = Cudd_bddAnd(manager, trans_ret, tmp2);
	Cudd_Ref(tmp1);
	FREE_BDD(tmp2);
	trans_ret = tmp1;
	

	// Add envTrans

	tmp2 = Cudd_bddAnd(manager, util1, in1);
	Cudd_Ref(tmp2);
	tmp1 = Cudd_bddIte(manager,
		tmp2,
		envTrans,
		Cudd_ReadOne(manager)
	);
	Cudd_Ref(tmp1);
	FREE_BDD(tmp2);

	tmp2 = Cudd_bddAnd(manager, trans_ret, tmp1);
	Cudd_Ref(tmp2);
	FREE_BDD(tmp1);
	trans_ret = tmp2;

	FREE_BDD(util0);
	FREE_BDD(util1);
	FREE_BDD(in0);
	FREE_BDD(in1);
	FREE_BDD(jn0);
	FREE_BDD(jn1);

	return trans_ret;
}

DdNode* getFixpointsBDD(DdManager* manager, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int* kindices, int kindicesSize) {

	DdNode *currI, *currJ, *currK, *tmp1, *tmp2, *currLevel, *currJustice;
	DdNode* fixpoints_ret = Cudd_ReadOne(manager);
	Cudd_Ref(fixpoints_ret);

	//int maxK = 0;
	//for (int j = 0; j < gr1_mem.sizeD1; j++) {
	//	if (gr1_mem.sizeD3[j] > maxK) {
	//		maxK = gr1_mem.sizeD3[j];
	//	}
	//}

	//int nind_to, nind_from, mind_to, mind_from, kind_to, kind_from;
	//createUtilVar(gr1_mem.sizeD1, &nind_from, &nind_to);
	//createUtilVar(gr1_mem.sizeD2, &mind_from, &mind_to);
	//createUtilVar(maxK, &kind_from, &kind_to);

	//Cudd_AutodynDisable(manager);

	for (int j = 0; j < gr1_mem.sizeD1; j++) {

		currJustice = Cudd_ReadOne(manager);
		Cudd_Ref(currJustice);
		for (int k = 0; k < gr1_mem.sizeD3[j]; k++) {

			currLevel = Cudd_ReadOne(manager);
			Cudd_Ref(currLevel);
			for (int i = 0; i < gr1_mem.sizeD2; i++) {

				currJ = ithVarInteger(manager, jindices, jindicesSize, j);
				currK = ithVarInteger(manager, kindices, kindicesSize, k);
				currI = ithVarInteger(manager, iindices, iindicesSize, i);

				tmp1 = Cudd_bddAnd(manager, currJ, currK);
				Cudd_Ref(tmp1);
				tmp2 = Cudd_bddAnd(manager, tmp1, currI);
				Cudd_Ref(tmp2);
				FREE_BDD(tmp1);
				tmp1 = Cudd_bddIte(manager,
					tmp2,
					gr1_mem.x_mem[j][i][k],
					Cudd_ReadOne(manager)
				);
				Cudd_Ref(tmp1);
				FREE_BDD(tmp2);

				tmp2 = Cudd_bddAnd(manager, currLevel, tmp1);
				Cudd_Ref(tmp2);
				FREE_BDD(tmp1);
				currLevel = tmp2;

				FREE_BDD(currI);
				FREE_BDD(currJ);
				FREE_BDD(currK);
			}

			tmp1 = Cudd_bddAnd(manager, currJustice, currLevel);
			Cudd_Ref(tmp1);
			FREE_BDD(currLevel);
			FREE_BDD(currJustice);
			currJustice = tmp1;
		}

		tmp1 = Cudd_bddAnd(manager, fixpoints_ret, currJustice);
		Cudd_Ref(tmp1);
		FREE_BDD(currJustice);
		FREE_BDD(fixpoints_ret);
		fixpoints_ret = tmp1;
	}

	//Cudd_AutodynEnable(manager, CUDD_REORDER_SAME);

	return fixpoints_ret;
}







void freeBDD(DdNode* bdd)
{
	if (bdd == NULL) return;
	Cudd_RecursiveDeref(manager, bdd);
}

void extend_size_3D(DdNode**** in, int sizeD1, int sizeD2, int newSize)
{
	int size1 = sizeof(in);
	DdNode** res;
	printf("extend_size_3D: newSize = %d\n", newSize);
	for (int i = 0; i < sizeD1; i++) {
		for (int j = 0; j < sizeD2; j++) {
			res = realloc(in[i][j], newSize * sizeof(DdNode*));
			if (res == NULL) {
				printf("ERROR: can't realloc in extend_size_3D!\n");
				return;
			}

			in[i][j] = res;
		}
	}
	printf("extend_size_3D end\n");
}

void print_inc_type(int type_bitmap)
{
	printf("INC_TYPE_PREV_INI_REMOVED = %d, INC_TYPE_PREV_SAFETY_REMOVED = %d, INC_TYPE_PREV_JUSTICE_REMOVED = %d \
			\nINC_TYPE_NEW_INI_ADDED = %d, INC_TYPE_NEW_SAFETY_ADDED = %d, INC_TYPE_NEW_JUSTICE_ADDED = %d\n", 
		IS_BIT_ON(type_bitmap, INC_TYPE_PREV_INI_REMOVED), IS_BIT_ON(type_bitmap, INC_TYPE_PREV_SAFETY_REMOVED), 
		IS_BIT_ON(type_bitmap, INC_TYPE_PREV_JUSTICE_REMOVED), IS_BIT_ON(type_bitmap, INC_TYPE_NEW_INI_ADDED), 
		IS_BIT_ON(type_bitmap, INC_TYPE_NEW_SAFETY_ADDED), IS_BIT_ON(type_bitmap, INC_TYPE_NEW_JUSTICE_ADDED));
}

int is_inc_only_ini(int type_bitmap)
{
	return ((IS_BIT_ON(type_bitmap, INC_TYPE_PREV_INI_REMOVED) && !IS_BIT_ON(type_bitmap, INC_TYPE_PREV_SAFETY_REMOVED) && !IS_BIT_ON(type_bitmap, INC_TYPE_PREV_JUSTICE_REMOVED))
		|| (IS_BIT_ON(type_bitmap, INC_TYPE_NEW_INI_ADDED) && !IS_BIT_ON(type_bitmap, INC_TYPE_NEW_SAFETY_ADDED) && !IS_BIT_ON(type_bitmap, INC_TYPE_NEW_JUSTICE_ADDED)));
}