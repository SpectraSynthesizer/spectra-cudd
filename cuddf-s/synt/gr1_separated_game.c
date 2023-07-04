/*
*	Implementation of the the GR1 game related functions from synt.h
*/

#include "synt.h"
#include "cuddInt.h"
#include <stdio.h>

/*
* The set of states from which the system and environment can together reach "toPrime" in a single step
*/
DdNode* prev(DdNode* to, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs, DdNode* sysTrans, DdNode* envTrans, int sca)
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
	DdNode* combinedTrans = Cudd_bddAnd(manager, sysTrans, envTrans);
	Cudd_Ref(combinedTrans);
	//DdNode* primedVars = Cudd_bddOr(manager, sysPrimeVars, envPrimeVars);
	//Cudd_Ref(primedVars);
	DdNode* transAndTo = Cudd_bddAnd(manager, combinedTrans, toPrime);
	Cudd_Ref(transAndTo);
	DdNode* preResult = Cudd_bddExistAbstract(manager, transAndTo, envPrimeVars);
	Cudd_Ref(preResult);
	DdNode* result = Cudd_bddExistAbstract(manager, preResult, sysPrimeVars);
	//DdNode* result = Cudd_bddExistAbstract(manager, transAndTo, primedVars);
	Cudd_Ref(result);
	Cudd_RecursiveDeref(manager, transAndTo);
	//Cudd_RecursiveDeref(manager, primedVars);
	Cudd_RecursiveDeref(manager, combinedTrans);
	Cudd_RecursiveDeref(manager, toPrime);
	Cudd_RecursiveDeref(manager, preResult);
	return result;
}



int gr1_separated_game(DdNode** sysJ, int sysJSize, DdNode** envJ, int envJSize, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysUnprime, DdNode* envUnprime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	int efp, int eun, int fpr, int sca)
{
	inc_gr1_data inc_data;


	return gr1_separated_game_inc(sysJ, sysJSize, envJ, envJSize, sysIni, envIni, sysTrans, envTrans,
		sysUnprime, envUnprime, sysPrimeVars, envPrimeVars, pairs,
		efp, eun, fpr, sca, false, inc_data);
}

int gr1_separated_game_inc(DdNode** sysJ, int sysJSize, DdNode** envJ, int envJSize, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysUnprime, DdNode* envUnprime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	int efp, int eun, int fpr, int sca, int isInc, inc_gr1_data inc_data)
{
	//printf("\n----Start GR1 Game: efp=%d, eun=%d, fpr=%d----\n", efp, eun, fpr); fflush(stdout);
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

	DdNode* x = NULL, * y, * z, * w;
	DdNode* xPrev, * yPrev, * zPrev, * wPrev;

	int* cy_mem = malloc(sysJSize * sizeof(int));
	memset(cy_mem, -1, sysJSize * sizeof(int));
	int cy = 0; // count y
	int firstZIter = true;

	//First - Z fixed point
	z = Cudd_ReadOne(manager);
	Cudd_Ref(Cudd_Regular(z));
	zPrev = NULL;
	yPrev = NULL;
	wPrev = NULL;
	int j_start_idx = 0;

	int zIters = 0;
	int yIters = 0;
	int xIters = 0;
	int wIters = 0;

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

		FREE_BDD(zPrev);
		zPrev = z;
		Cudd_Ref(zPrev);

		//TODO: TMP - can handle justice removes without xMem
		if (isInc && firstZIter) handle_inc_only_j_removed(inc_data, &j_start_idx, &z, currSize, cy_mem);

		for (int j = j_start_idx; j < sysJSize; j++)
		{
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
			///Second - Y fixed point 
			while (yPrev == NULL || !IS_BDD_EQ(y, yPrev))
			{
				yIters++;
				ytmp++;

				FREE_BDD(yPrev);
				yPrev = y;
				Cudd_Ref(yPrev);
				
				DdNode* yieldStatesY = yield(y, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
				DdNode* start = Cudd_bddOr(manager, yieldStatesZToJ, yieldStatesY);
				Cudd_Ref(start);
				FREE_BDD(yieldStatesY);

				FREE_BDD(y);
				y = Cudd_Not(Cudd_ReadOne(manager));
				Cudd_Ref(y);

				for (int i = 0; i < envJSize; i++)
				{
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
							}
							else {
								//printf("recycleFixPoint X for j=%d, i=%d, rcy=%d\n", j, i, rcy);
								x = Cudd_bddAnd(manager, gr1_mem.x_mem[j][i][rcy], z);
								Cudd_Ref(x);
							}
						}
						else if (rcy != -1) {
							//printf("recycleFixPoint X for j=%d, i=%d, rcy=%d\n", j, i, rcy);
							DdNode* tmp = Cudd_bddAnd(manager, gr1_mem.x_mem[j][i][rcy], x);
							Cudd_Ref(tmp);
							FREE_BDD(x);
							x = tmp;
						}
					}
					else if (!isInc) {
						x = z;
						Cudd_Ref(x);
					}

					xPrev = NULL;
					// Third - X fixed point
					//printf("x loop start\n"); fflush(stdout);
					while (xPrev == NULL || !IS_BDD_EQ(x, xPrev))
					{
						xIters++;
						xtmp++;
						FREE_BDD(xPrev);
						xPrev = x;
						Cudd_Ref(xPrev);
						DdNode* xAndNegEnvJ = Cudd_bddAnd(manager, x, negEnvJ);
						Cudd_Ref(xAndNegEnvJ);

						w = Cudd_Not(Cudd_ReadOne(manager));
						Cudd_Ref(w);
						while (wPrev == NULL || !IS_BDD_EQ(w, wPrev)) {
							wIters++;
							FREE_BDD(wPrev);
							wPrev = w;
							Cudd_Ref(wPrev);
							DdNode* wOrXAndNegEnvJ = Cudd_bddOr(manager, w, xAndNegEnvJ);
							Cudd_Ref(wOrXAndNegEnvJ);
							DdNode* yieldWOrXAndNegEnvJ = yield(wOrXAndNegEnvJ, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
							FREE_BDD(wOrXAndNegEnvJ);
							DdNode* preExistW = prev(w, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
							DdNode* condPre = Cudd_bddAnd(manager, preExistW, yieldWOrXAndNegEnvJ);
							Cudd_Ref(condPre);
							FREE_BDD(yieldWOrXAndNegEnvJ);
							FREE_BDD(preExistW);
							DdNode* rhs = Cudd_bddAnd(manager, negEnvJ, condPre);
							Cudd_Ref(rhs);
							FREE_BDD(condPre);
							FREE_BDD(w);
							w = Cudd_bddOr(manager, rhs, start);
							Cudd_Ref(w);
							FREE_BDD(rhs);
						}
						FREE_BDD(wPrev);
						FREE_BDD(x);
						FREE_BDD(xAndNegEnvJ);
						x = w;
						Cudd_Ref(x);
					} // End X fixed point
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
			FREE_BDD(yPrev); 
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
	//printf("z loop end\n"); fflush(stdout);
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
	return is_real;
}
