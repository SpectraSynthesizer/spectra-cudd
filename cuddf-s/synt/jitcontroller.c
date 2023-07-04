#include "jitcontroller.h"

// Since CuddPairing is symmetric (a->b means b->a in the list) prime and unprime are the same
DdNode* unprime(DdNode* bdd, CuddPairing* pairs) {
	return prime(bdd, pairs);
}

DdNode* prime(DdNode* bdd, CuddPairing* pairs) {

	int varnum = Cudd_ReadSize(manager);
	unsigned int* arr = (unsigned int*) malloc(sizeof(unsigned int) * varnum);

	if (arr == NULL) {
		fflush(stdout);
		return INVALID_BDD;
	}

	for (int i = 0; i < varnum; ++i) {
		DdNode* node = pairs->table[i];
		unsigned int var = Cudd_NodeReadIndex(node);
		arr[i] = var;
	}
	DdNode* primed = Cudd_bddPermute(manager, bdd, arr);
	Cudd_Ref(primed);
	free(arr);

	return primed;
}

void loadFixpoints(DdNode* fixpoints, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int* kindices, int kindicesSize, int* ranks_arr, 
	CuddPairing* pairs, DdNode* primeVars) {

	ranks = (int*) malloc(sizeof(int) * n);
	memcpy(ranks, ranks_arr, sizeof(int) * n);

	mX = malloc(n * sizeof(DdNode***));
	mY = malloc(n * sizeof(DdNode**));
	for (int j = 0; j < n; j++)
	{
		mX[j] = malloc(m * sizeof(DdNode**));
		for (int i = 0; i < m; i++)
		{
			mX[j][i] = malloc(ranks[j] * sizeof(DdNode*));
		}
		mY[j] = malloc(ranks[j] * sizeof(DdNode*));
	}

	DdNode *currI, *currJ, *currR, *tmp1, *tmp2, *unprimed_x;

	for (int j = 0; j < n; j++) {
		for (int r = 0; r < ranks[j]; r++) {

			mY[j][r] = Cudd_Not(Cudd_ReadOne(manager));
			Cudd_Ref(mY[j][r]);
			for (int i = 0; i < m; i++) {

				currJ = ithVarInteger(manager, jindices, jindicesSize, j);
				currR = ithVarInteger(manager, kindices, kindicesSize, r);
				currI = ithVarInteger(manager, iindices, iindicesSize, i);

				tmp1 = Cudd_bddAnd(manager, currJ, currR);
				Cudd_Ref(tmp1);
				tmp2 = Cudd_bddAnd(manager, tmp1, currI);
				Cudd_Ref(tmp2);
				FREE_BDD(tmp1);
				unprimed_x = Cudd_Cofactor(manager, fixpoints, tmp2);
				Cudd_Ref(unprimed_x);
				FREE_BDD(tmp2);
				mX[j][i][r] = prime(unprimed_x, pairs);
				FREE_BDD(unprimed_x);

				tmp1 = Cudd_bddOr(manager, mY[j][r], mX[j][i][r]);
				Cudd_Ref(tmp1);
				FREE_BDD(mY[j][r]);
				mY[j][r] = tmp1;

				FREE_BDD(currI);
				FREE_BDD(currR);
				FREE_BDD(currJ);
			}
		}
	}

	transitions = Cudd_bddAnd(manager, sysTrans, envTrans);
	Cudd_Ref(transitions);

	initial = Cudd_bddAnd(manager, sysIni, envIni);
	Cudd_Ref(initial);

	DdNode* Z = unprime(mY[0][ranks[0] - 1], pairs);
	DdNode* tmp = Cudd_bddExistAbstract(manager, initial, primeVars);
	Cudd_Ref(tmp);
	FREE_BDD(initial);
	initial = Cudd_bddAnd(manager, tmp, Z);
	Cudd_Ref(initial);
	FREE_BDD(tmp);
	FREE_BDD(Z);
}

void loadTrans(DdNode* trans, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int utilindex) {

	DdNode* tmp;
	DdNode* util0 = Cudd_Not(Cudd_bddIthVar(manager, utilindex));
	DdNode* jn0 = ithVarInteger(manager, jindices, jindicesSize, 0);
	DdNode* in0 = ithVarInteger(manager, iindices, iindicesSize, 0);
	DdNode* util1 = Cudd_bddIthVar(manager, utilindex);
	DdNode* jn1 = ithVarInteger(manager, jindices, jindicesSize, 1);
	DdNode* in1 = ithVarInteger(manager, iindices, iindicesSize, 1);

	// Load sysIni
	tmp = Cudd_bddAnd(manager, util0, jn0);
	Cudd_Ref(tmp);
	sysIni = Cudd_Cofactor(manager, trans, tmp);
	Cudd_Ref(sysIni);
	FREE_BDD(tmp);

	// Load envIni
	tmp = Cudd_bddAnd(manager, util1, in0);
	Cudd_Ref(tmp);
	envIni = Cudd_Cofactor(manager, trans, tmp);
	Cudd_Ref(envIni);
	FREE_BDD(tmp);

	// Load sysTrans
	tmp = Cudd_bddAnd(manager, util0, jn1);
	Cudd_Ref(tmp);
	sysTrans = Cudd_Cofactor(manager, trans, tmp);
	Cudd_Ref(sysTrans);
	FREE_BDD(tmp);

	// Load envTrans
	tmp = Cudd_bddAnd(manager, util1, in1);
	Cudd_Ref(tmp);
	envTrans = Cudd_Cofactor(manager, trans, tmp);
	Cudd_Ref(envTrans);
	FREE_BDD(tmp);

	FREE_BDD(util0);
	FREE_BDD(util1);
	FREE_BDD(in0);
	FREE_BDD(in1);
	FREE_BDD(jn0);
	FREE_BDD(jn1);
}

void loadJustices(DdNode* justices, int* jindices, int jindicesSize, int* iindices, int iindicesSize, int utilindex, int newn, int newm) {

	n = newn;
	m = newm;
	DdNode *currI, *currJ, *tmp;
	justice_gar = malloc(n * sizeof(DdNode*));
	justice_asm = malloc(m * sizeof(DdNode*));

	DdNode* util0 = Cudd_Not(Cudd_bddIthVar(manager, utilindex));

	for (int j = 0; j < n; j++) {

		currJ = ithVarInteger(manager, jindices, jindicesSize, j);
		tmp = Cudd_bddAnd(manager, util0, currJ);
		Cudd_Ref(tmp);
		justice_gar[j] = Cudd_Cofactor(manager, justices, tmp);
		Cudd_Ref(justice_gar[j]);
		FREE_BDD(tmp);
		FREE_BDD(currJ);
	}

	DdNode* util1 = Cudd_bddIthVar(manager, utilindex);

	for (int i = 0; i < m; i++) {

		currI = ithVarInteger(manager, iindices, iindicesSize, i);
		tmp = Cudd_bddAnd(manager, util1, currI);
		Cudd_Ref(tmp);
		justice_asm[i] = Cudd_Cofactor(manager, justices, tmp);
		Cudd_Ref(justice_asm[i]);
		FREE_BDD(tmp);
		FREE_BDD(currI);
	}

	FREE_BDD(util0);
	FREE_BDD(util1);
}

DdNode* nextStatesController(DdNode* current, DdNode* inputs, CuddPairing* pairs, DdNode* unprimeVars) {

	DdNode *nextStates, *tmp;
	tmp = Cudd_bddAnd(manager, transitions, current);
	Cudd_Ref(tmp);
	DdNode* inputsPrimed = prime(inputs, pairs);

	DdNode* transAndInputs = Cudd_bddAnd(manager, tmp, inputsPrimed);
	Cudd_Ref(transAndInputs);
	FREE_BDD(tmp);

	DdNode* zero = Cudd_Not(Cudd_ReadOne(manager));
	Cudd_Ref(zero);

	if (rx == 0) {

		DdNode* currentWithJusticeGoal = Cudd_bddAnd(manager, justice_gar[jx], current);
		Cudd_Ref(currentWithJusticeGoal);

		if (!IS_BDD_EQ(currentWithJusticeGoal, zero)) {

			//printf("rho1 with jx=%d\n", jx);
			jx = (jx + 1) % n;

			int r = findNextRank(jx, 0, ranks[jx] - 1, transAndInputs);
			nextStates = Cudd_bddAnd(manager, transAndInputs, mY[jx][r]);
			Cudd_Ref(nextStates);
			ix = -1;
			rx = r;
			//printf("rho1 with new jx=%d and next rx=%d\n", jx, rx);


			//int found = 0;

			//for (int r = 0; r < ranks[jx]; r++) {
			//	tmp = Cudd_bddAnd(manager, transAndInputs, mY[jx][r]);
			//	Cudd_Ref(tmp);

			//	if (!IS_BDD_EQ(tmp, zero)) {
			//		nextStates = tmp;
			//		ix = -1;
			//		rx = r;
			//		found = 1;
			//		//printf("rho1 with new jx=%d and next rx=%d\n", jx, rx);
			//		break;
			//	}

			//	FREE_BDD(tmp);
			//}

			//if (found == 0) {
			//	printf("Impossible to compute next state rho1 with jx=%d\n", jx);
			//	fflush(stdout);
			//	return INVALID_BDD;
			//}

		} else {

			if (ix == -1) {

				DdNode* currentPrimed = prime(current, pairs);
				int found = 0;

				for (int i = 0; i < m; i++) {
					tmp = Cudd_bddAnd(manager, currentPrimed, mX[jx][i][0]);
					Cudd_Ref(tmp);

					if (!IS_BDD_EQ(tmp, zero)) {
						FREE_BDD(tmp);
						ix = i;
						found = 1;
						break;
					}

					FREE_BDD(tmp);
				}

				if (found == 0) {
					printf("Impossible to compute next state rho3 with jx=%d and rx=%d\n", jx, rx);
					fflush(stdout);
					return INVALID_BDD;
				}
			}

			nextStates = Cudd_bddAnd(manager, transAndInputs, mX[jx][ix][0]);
			Cudd_Ref(nextStates);
			//printf("rho3 with jx=%d and rx=0 and ix=%d\n", jx, ix);
		}

		FREE_BDD(currentWithJusticeGoal);

	} else {

		tmp = Cudd_bddAnd(manager, transAndInputs, mY[jx][rx-1]);
		Cudd_Ref(tmp);

		if (!IS_BDD_EQ(tmp, zero)) {

			int r = findNextRank(jx, 0, rx - 1, transAndInputs);
			nextStates = Cudd_bddAnd(manager, transAndInputs, mY[jx][r]);
			Cudd_Ref(nextStates);
			//printf("rho2 with jx=%d and rx=%d and next rx=%d\n", jx, rx, r);
			ix = -1;
			rx = r;

			//int found = 0;
			//DdNode* tmp2;

			//for (int r = rx - 1; r > 0; r--) {
			//	tmp2 = Cudd_bddAnd(manager, transAndInputs, mY[jx][r-1]);
			//	Cudd_Ref(tmp2);

			//	if (IS_BDD_EQ(tmp2, zero)) {
			//		FREE_BDD(tmp2);
			//		nextStates = tmp;
			//		//printf("rho2 with jx=%d and rx=%d and next rx=%d\n", jx, rx, r);
			//		ix = -1;
			//		rx = r;
			//		found = 1;
			//		break;
			//	}

			//	FREE_BDD(tmp);
			//	tmp = tmp2;
			//}

			//if (found == 0) {
			//	nextStates = tmp;
			//	//printf("rho2 with jx=%d and rx=%d and next rx=0\n", jx, rx);
			//	ix = -1;
			//	rx = 0;
			//}

		} else {

			FREE_BDD(tmp);

			if (ix == -1) {

				DdNode* currentPrimed = prime(current, pairs);
				int found = 0;

				for (int i = 0; i < m; i++) {
					tmp = Cudd_bddAnd(manager, currentPrimed, mX[jx][i][rx]);
					Cudd_Ref(tmp);

					if (!IS_BDD_EQ(tmp, zero)) {
						FREE_BDD(tmp);
						ix = i;
						found = 1;
						break;
					}

					FREE_BDD(tmp);
				}

				if (found == 0) {
					printf("Impossible to compute next state rho3 with jx=%d and rx=%d\n", jx, rx);
					fflush(stdout);
					return INVALID_BDD;
				}
			}

			nextStates = Cudd_bddAnd(manager, transAndInputs, mX[jx][ix][rx]);
			Cudd_Ref(nextStates);
			//printf("rho3 with jx=%d and rx=%d and ix=%d\n", jx, rx, ix);
		}
	}

	FREE_BDD(zero);
	FREE_BDD(transAndInputs);
	DdNode* primedNextStates = Cudd_bddExistAbstract(manager, nextStates, unprimeVars);
	Cudd_Ref(primedNextStates);
	FREE_BDD(nextStates);
	nextStates = unprime(primedNextStates, pairs);
	FREE_BDD(primedNextStates);
	return nextStates;
}

int findNextRank(int j, int from, int to, DdNode* conjunct) {

	DdNode* zero = Cudd_Not(Cudd_ReadOne(manager));
	Cudd_Ref(zero);
	DdNode* tmp;
	int r;

	//printf("begin findNextRank from=%d, to=%d\n", from, to);

	while (from != to) {
	
		r = (int) ((from + to) / 2);
		tmp = Cudd_bddAnd(manager, conjunct, mY[j][r]);
		Cudd_Ref(tmp);

		if (IS_BDD_EQ(tmp, zero)) {
			from = r + 1;
		} else {
			to = r;
		}

		//printf("findNextRank from=%d, to=%d\n", from, to);

		FREE_BDD(tmp);
	}

	//printf("end findNextRank from=%d, to=%d\n", from, to);
	
	FREE_BDD(zero);
	return from;
}

int initController(DdNode* current, CuddPairing* pairs) {

	printf("n=%d, m=%d\n", n, m);
	for (int j = 0; j < n; j++) {
		printf("r=%d\n", ranks[j]);
	}

	DdNode* currentPrimed = prime(current, pairs);

	ix = -1;
	rx = findNextRank(0, 0, ranks[0] - 1, currentPrimed);

	//int found = 0;

	//for (int r = 0; r < ranks[0]; r++) {
	//	tmp = Cudd_bddAnd(manager, initialAndInputs, mY[0][r]);
	//	Cudd_Ref(tmp);

	//	if (!IS_BDD_EQ(tmp, zero)) {
	//		FREE_BDD(tmp);
	//		ix = -1;
	//		rx = r;
	//		found = 1;
	//		break;
	//	}

	//	FREE_BDD(tmp);
	//}

	//// Error to be caught in Java level
	//if (found == 0) {
	//	return -1;
	//}

	FREE_BDD(sysIni);
	FREE_BDD(envIni);

	return 0;
}

void freeController() {

	FREE_BDD(sysTrans);
	FREE_BDD(envTrans);
	FREE_BDD(sysIni);
	FREE_BDD(envIni);
	FREE_BDD(transitions);
	FREE_BDD(initial);

	for (int j = 0; j < n; ++j) {
		FREE_BDD(justice_gar[j]);
	}

	for (int i = 0; i < m; ++i) {
		FREE_BDD(justice_asm[i]);
	}

	for (int j = 0; j < n; ++j) {
		for (int r = 0; r < ranks[j]; r++) {
			for (int i = 0; i < m; ++i) {
				FREE_BDD(mX[j][i][r]);
			}
			FREE_BDD(mY[j][r]);
		}
	}

	free(ranks);
}