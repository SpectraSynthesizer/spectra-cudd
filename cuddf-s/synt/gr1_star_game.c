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
*	Implementation of the the GR1-STAR game related functions from synt.h
*/
#include "synt.h"
#include "cuddInt.h"
#include <stdio.h>

/*
* Free the memory that was allocated in gr1_star_game
*/
void free_gr1_star_mem(void)
{
	if (gr1_star_mem.x_mem != NULL || gr1_star_mem.y_mem != NULL) {
		for (int i = 0; i < gr1_star_mem.x_y_z_sizeD1; i++)
		{
			if (gr1_star_mem.x_mem != NULL) {
				for (int j = 0; j < gr1_star_mem.x_sizeD2; j++)
				{
					free(gr1_star_mem.x_mem[i][j]);
				}
				free(gr1_star_mem.x_mem[i]);
			}

			if (gr1_star_mem.y_mem != NULL) free(gr1_star_mem.y_mem[i]);
		}

		if (gr1_star_mem.x_mem != NULL) free(gr1_star_mem.x_mem);
		if (gr1_star_mem.y_mem != NULL) free(gr1_star_mem.y_mem);

		gr1_star_mem.x_mem = NULL;
		gr1_star_mem.y_mem = NULL;
	}
	
	if (gr1_star_mem.x_sizeD3 != NULL)
	{
		free(gr1_star_mem.x_sizeD3);
		gr1_star_mem.x_sizeD3 = NULL;
	}

	if (gr1_star_mem.z_mem != NULL)
	{
		//for (int j = 0; j < gr1_star_mem.x_y_z_sizeD1; j++) {
		//	FREE_BDD(gr1_star_mem.z_mem[j]);
		//}
		free(gr1_star_mem.z_mem);
		gr1_star_mem.z_mem = NULL;
	}

	if (gr1_star_mem.envJ_violation_mem != NULL) {
		for (int i = 0; i < gr1_star_mem.x_sizeD2; i++) {
			free(gr1_star_mem.envJ_violation_mem[i]);
		}
		free(gr1_star_mem.envJ_violation_mem);
		gr1_star_mem.envJ_violation_mem = NULL;
	}

	if (gr1_star_mem.fulfill_exist_mem != NULL) {
		for (int k = 0; k < gr1_star_mem.exist_sizeD1; k++) {
			free(gr1_star_mem.fulfill_exist_mem[k]);
		}
		free(gr1_star_mem.fulfill_exist_mem);
		gr1_star_mem.fulfill_exist_mem = NULL;
	}

	if (gr1_star_mem.towards_exist_mem != NULL) {
		for (int k = 0; k < gr1_star_mem.exist_sizeD1; k++) {
			free(gr1_star_mem.towards_exist_mem[k]);
		}
		free(gr1_star_mem.towards_exist_mem);
		gr1_star_mem.towards_exist_mem = NULL;
	}

	if (gr1_star_mem.fulfill_exist_sizeD2 != NULL) {
		free(gr1_star_mem.fulfill_exist_sizeD2);
		gr1_star_mem.fulfill_exist_sizeD2 = NULL;
	}

	gr1_star_mem.x_y_z_sizeD1 = 0;
	gr1_star_mem.x_sizeD2 = 0;

	gr1_star_mem.envJ_violation_sizeD2 = 0;
	gr1_star_mem.exist_sizeD1 = 0;
}

int init_memory(int justiceIterCurrSize, int fulfillExistIterCurrSize, int towardsExistIterCurrSize,
	int jViolationIterCurrSize, int sysJSize, int envJSize) {
	gr1_star_mem.x_y_z_sizeD1 = sysJSize;
	gr1_star_mem.x_sizeD2 = envJSize;

	gr1_star_mem.x_mem = malloc(sysJSize * sizeof(DdNode***));
	gr1_star_mem.y_mem = malloc(sysJSize * sizeof(DdNode**));
	gr1_star_mem.z_mem = malloc(sysJSize * sizeof(DdNode*));
	for (int sysJi = 0; sysJi < sysJSize; sysJi++)
	{
		gr1_star_mem.x_mem[sysJi] = malloc(envJSize * sizeof(DdNode**));
		for (int envJi = 0; envJi < envJSize; envJi++)
		{
			gr1_star_mem.x_mem[sysJi][envJi] = malloc(justiceIterCurrSize * sizeof(DdNode*));
		}
		gr1_star_mem.y_mem[sysJi] = malloc(justiceIterCurrSize * sizeof(DdNode*));
	}

	if (exist_gars_list.isInit) { //there are existential guarantees
		gr1_star_mem.exist_sizeD1 = exist_gars_list.listSize;
		gr1_star_mem.fulfill_exist_mem = malloc(gr1_star_mem.exist_sizeD1 * sizeof(DdNode**));
		gr1_star_mem.towards_exist_mem = malloc(gr1_star_mem.exist_sizeD1 * sizeof(DdNode**));

		for (int k = 0; k < gr1_star_mem.exist_sizeD1; k++) {
			gr1_star_mem.fulfill_exist_mem[k] = malloc(fulfillExistIterCurrSize * sizeof(DdNode*));
			gr1_star_mem.towards_exist_mem[k] = malloc(towardsExistIterCurrSize * sizeof(DdNode*));
		}

		gr1_star_mem.envJ_violation_mem = malloc(envJSize * sizeof(DdNode**));

		for (int envJi = 0; envJi < envJSize; envJi++) {
			gr1_star_mem.envJ_violation_mem[envJi] = malloc(jViolationIterCurrSize * sizeof(DdNode*));
		}
	}
}

DdNode* compute_justice_iteration(DdNode* z, int firstZIter, int* currSize, DdNode** sysJ, int sysJSize,
	DdNode** envJ, int envJSize, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	int efp, int fpr, int sca, int mem, int* cy_mem) {

	DdNode *x, *y, *zApprox = z;
	Cudd_Ref(zApprox);
	
	DdNode *xPrev, *yPrev; // ;, *zPrev;

	//int* cy_mem = malloc(sysJSize * sizeof(int));
	//memset(cy_mem, -1, sysJSize * sizeof(int));
	int cy; //= 0; // count y
	//int firstZIter = true; //given as an input argument

	//First - Z fixed point
	//zApprox = Cudd_ReadOne(manager);
	
	//zPrev = NULL;
	//yPrev = NULL;
	//int j_start_idx = 0;

	////printf("Z loop - before\n");
	//Cudd_DebugCheck(manager);
	//Cudd_CheckKeys(manager);

	//int zIters = 0;
	//int yIters = 0;
	//int xIters = 0;

	//int xtmp = 0;
	//int ytmp = 0;

	//int isFinished = false;


	//while (zPrev == NULL || !IS_BDD_EQ(zApprox, zPrev))
	//{
		//zIters++;

		//if (zPrev == NULL) //printf("zPrev is NULL\n");
		//if (zPrev != NULL) //printf("IS_BDD_EQ(z, zPrev) = %d\n", IS_BDD_EQ(z, zPrev));

		//FREE_BDD(zPrev);
		//zPrev = zApprox;
		//Cudd_Ref(zPrev);

		for (int j = 0; j < sysJSize; j++)
		{
			//printf("Z loop %d: j = %d\n", zIters, j); 
			//fflush(stdout);
			//Cudd_DebugCheck(manager);
			//Cudd_CheckKeys(manager);

			DdNode* yieldStatesZ = yield(zApprox, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
			DdNode* yieldStatesZToJ = Cudd_bddAnd(manager, sysJ[j], yieldStatesZ);
			Cudd_Ref(yieldStatesZToJ);
			FREE_BDD(yieldStatesZ);

			cy = 0;
			y = Cudd_Not(Cudd_ReadOne(manager));
			Cudd_Ref(y);
			//FREE_BDD(yPrev);
			yPrev = NULL;

			//Y fixed-point iteration 
			while (yPrev == NULL || !IS_BDD_EQ(y, yPrev))
			{
				//yIters++;
				//ytmp++;
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

					//FREE_BDD(x);
					
					DdNode* negEnvJ = Cudd_Not(envJ[i]);
					Cudd_Ref(negEnvJ);

					if (mem && fpr && !firstZIter)
					{
						//int rcy = -1;
						//if (cy < cy_mem[j])
						//{
						//	rcy = cy;
						//}
						if (cy >= cy_mem[j]) {
							x = zApprox;
							Cudd_Ref(x);
						}
						else {
							//printf("recycleFixPoint X for j=%d, i=%d, rcy=%d\n", j, i, cy);
							x = Cudd_bddAnd(manager, gr1_star_mem.x_mem[j][i][cy], zApprox);
							Cudd_Ref(x);
						}
					}
					else {
						x = zApprox;
						Cudd_Ref(x);
					}

					xPrev = NULL;
					//X fixed-point iteration
					while (xPrev == NULL || !IS_BDD_EQ(x, xPrev))
					{
						//xIters++;
						//xtmp++;
						////printf("X loop - start\n"); fflush(stdout);
						//Cudd_DebugCheck(manager);
						//Cudd_CheckKeys(manager);

						FREE_BDD(xPrev);
						xPrev = x;
						Cudd_Ref(xPrev);
						////printf("is x one = %d\n", x == Cudd_ReadOne(manager)); fflush(stdout);
						////printf("is xPrev one = %d\n", xPrev == Cudd_ReadOne(manager)); fflush(stdout);
						
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
					//xtmp = 0;
					FREE_BDD(xPrev);
					FREE_BDD(negEnvJ);
					////printf("j = %d, i = %d, cy = %d\n", j,i,cy); fflush(stdout);
					////printf("cy = %d, cy_mem[%d] = %d\n", cy,j, cy_mem[j]); fflush(stdout);
					
					if (mem) {
						if (cy < cy_mem[j]) {
							FREE_BDD(gr1_star_mem.x_mem[j][i][cy]);
						}
						gr1_star_mem.x_mem[j][i][cy] = x;
						Cudd_Ref(gr1_star_mem.x_mem[j][i][cy]);
					}

					DdNode* tmp = Cudd_bddOr(manager, y, x);
					Cudd_Ref(tmp);
					FREE_BDD(x);
					FREE_BDD(y);
					y = tmp;
				} // End loop over envJ
				  ////printf("j = %d, cy = %d\n", j,cy); fflush(stdout);
				FREE_BDD(start);
				
				if (mem) {
					if (cy < cy_mem[j]) {
						FREE_BDD(gr1_star_mem.y_mem[j][cy]);
					}

					gr1_star_mem.y_mem[j][cy] = y;
					Cudd_Ref(gr1_star_mem.y_mem[j][cy]);
					
					cy++;
					
					// extend size of x_mem and y_mem
					if (cy == *currSize) {
						*currSize = (*currSize) * 2;
						extend_size_3D(gr1_star_mem.x_mem, sysJSize, envJSize, *currSize);
						extend_size_2D(gr1_star_mem.y_mem, sysJSize, *currSize);
					}
				}
				////printf("IS_BDD_EQ(y, yPrev) = %d\n", IS_BDD_EQ(y, yPrev));
			} // End Y fixed point
			FREE_BDD(yPrev);
			FREE_BDD(yieldStatesZToJ);
			FREE_BDD(zApprox);
			zApprox = y;

			////printf("ytmp = %d\n", ytmp);
			//ytmp = 0;

		//	if (eun && !sysWinAllInitial(zApprox, sysIni, envIni, sysUnprime, envUnprime)) {
				//printf("sysWinAllInitial is false - detected early unrealizable\n");
		//		zApprox = Cudd_Not(Cudd_ReadOne(manager));
		//		isFinished = true;
		//		break;
		//	}

			if (mem && efp && !firstZIter) {
				////printf("firstZIter = %d\n", firstZIter);
				if (IS_BDD_EQ(gr1_star_mem.z_mem[j], zApprox)) {
					//printf("detected early fixed point\n");
					FREE_BDD(zApprox);
					zApprox = gr1_star_mem.z_mem[sysJSize - 1];
					Cudd_Ref(zApprox);	
					cy_mem[j] = cy;
					//isFinished = true;
					//break;
					return zApprox;
				}
			}

			if (mem) {
				//TODO: for each i save the last x_mem[j][i][cy_mem[j]] 
				cy_mem[j] = cy;
				if (!firstZIter) {
					FREE_BDD(gr1_star_mem.z_mem[j]);
				}
				gr1_star_mem.z_mem[j] = zApprox;
				Cudd_Ref(gr1_star_mem.z_mem[j]);
			}
		} // End loop over sysJ

		//j_start_idx = 0;
		//firstZIter = false;
		////printf("zPrev == NULL = %d\n", (zPrev == NULL));
		////printf("IS_BDD_EQ(z, zPrev) = %d\n", IS_BDD_EQ(z, zPrev));
		
		//if (isFinished) return;

	//} // End Z fixed point
		return zApprox;
}

DdNode* compute_env_assumption_violation(DdNode** envJ, int* currSize, int envJSize, DdNode* sysTrans,
	DdNode* envTrans, DdNode* sysPrimeVars,
	DdNode* envPrimeVars, CuddPairing* pairs, int sca, int mem) {
	
	DdNode *x, *xPrev, *y, *yPrev, *yieldStatesY, *negEnvJ, *yieldStatesX, *yieldStatesXnotToJ, *tmp;
	int cy = 0;

	//Y least fixed-point iteration 
	y = Cudd_Not(Cudd_ReadOne(manager));
	Cudd_Ref(y);
	yPrev = NULL;
	while (yPrev == NULL || !IS_BDD_EQ(y, yPrev))
	{
		FREE_BDD(yPrev);
		yPrev = y;
		Cudd_Ref(yPrev);

		yieldStatesY = yield(y, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
		//Cudd_Ref(yieldStatesY);

		y = Cudd_Not(Cudd_ReadOne(manager));
		Cudd_Ref(y);

		for (int i = 0; i < envJSize; i++)
		{
			negEnvJ = Cudd_Not(envJ[i]);
			Cudd_Ref(negEnvJ);

			//X greatest fixed-point iteration
			x = Cudd_ReadOne(manager);
			Cudd_Ref(x);
			xPrev = NULL;
			while (xPrev == NULL || !IS_BDD_EQ(x, xPrev))
			{
				FREE_BDD(xPrev);
				xPrev = x;
				Cudd_Ref(xPrev);

				yieldStatesX = yield(x, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
				yieldStatesXnotToJ = Cudd_bddAnd(manager, yieldStatesX, negEnvJ);
				Cudd_Ref(yieldStatesXnotToJ);
				FREE_BDD(yieldStatesX);

				FREE_BDD(x);
				x = Cudd_bddOr(manager, yieldStatesXnotToJ, yieldStatesY);
				Cudd_Ref(x);

				FREE_BDD(yieldStatesXnotToJ);
			}//End of X iteration

			FREE_BDD(xPrev);
			FREE_BDD(negEnvJ);

			if (mem) {
				gr1_star_mem.envJ_violation_mem[i][cy] = x;
				Cudd_Ref(gr1_star_mem.envJ_violation_mem[i][cy]);
			}

			tmp = Cudd_bddOr(manager, y, x);
			Cudd_Ref(tmp);
			FREE_BDD(x);
			FREE_BDD(y);
			y = tmp;
		}
		FREE_BDD(yieldStatesY);
		if (mem) {
			cy++;
			if (cy == *currSize) {
				*currSize = (*currSize) * 2;
				extend_size_2D(gr1_star_mem.envJ_violation_mem, envJSize, *currSize);
			}
		}
	} //End of Y iteration
	FREE_BDD(yPrev);
	if (mem) {
		gr1_star_mem.envJ_violation_sizeD2 = cy;
	}
	return y;
}

DdNode* compute_exist_iteration(DdNode* z, int existGarIdx, int* fulfillCurrSize, int* towardsCurrSize, DdNode** sysJ, int sysJSize,
	DdNode** envJ, int envJSize, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	int sca, int mem, int* ctowards_exist_mem, int* cfulfill_exist_mem) {

	DdNode* lengthOneSfaWordSuffix = Cudd_bddAnd(manager, exist_gars_list.sfaTransToAccList[existGarIdx], z);
	Cudd_Ref(lengthOneSfaWordSuffix);

	DdNode *lengthKSfaWordSuffix = Cudd_Not(Cudd_ReadOne(manager));
	Cudd_Ref(lengthKSfaWordSuffix);

	DdNode *lengthKSfaWordSuffixPrev = NULL, *tmp;

	int c_fulfill = 0, c_towards = 0;

	while (lengthKSfaWordSuffixPrev == NULL || !IS_BDD_EQ(lengthKSfaWordSuffix, lengthKSfaWordSuffixPrev))
	{
		FREE_BDD(lengthKSfaWordSuffixPrev);
		lengthKSfaWordSuffixPrev = lengthKSfaWordSuffix;
		Cudd_Ref(lengthKSfaWordSuffixPrev);

		tmp = pred(lengthKSfaWordSuffix, existGarIdx, sysPrimeVars, envPrimeVars,
			pairs, sysTrans, envTrans, sca);

		FREE_BDD(lengthKSfaWordSuffix);
		
		lengthKSfaWordSuffix = Cudd_bddAnd(manager, z, tmp);
		Cudd_Ref(lengthKSfaWordSuffix);
		FREE_BDD(tmp);
		tmp = lengthKSfaWordSuffix;

		lengthKSfaWordSuffix = Cudd_bddOr(manager, lengthOneSfaWordSuffix, tmp);
		Cudd_Ref(lengthKSfaWordSuffix);
		FREE_BDD(tmp);

		if (mem) {
			//store current iteration
			if (c_fulfill < cfulfill_exist_mem[existGarIdx]) {
				FREE_BDD(gr1_star_mem.fulfill_exist_mem[existGarIdx][c_fulfill]);
			}
			gr1_star_mem.fulfill_exist_mem[existGarIdx][c_fulfill] = lengthKSfaWordSuffix;
			Cudd_Ref(gr1_star_mem.fulfill_exist_mem[existGarIdx][c_fulfill]);
			c_fulfill++;
			if (c_fulfill == *fulfillCurrSize) {
				*fulfillCurrSize = (*fulfillCurrSize) * 2;
				extend_size_2D(gr1_star_mem.fulfill_exist_mem, gr1_star_mem.exist_sizeD1, *fulfillCurrSize);
			}
		}
	}

	FREE_BDD(lengthKSfaWordSuffixPrev);
	FREE_BDD(lengthOneSfaWordSuffix);
	
	if (mem) {
		//free unused, older memory values
		int c_fulfill_tmp = c_fulfill;
		while (c_fulfill_tmp < cfulfill_exist_mem[existGarIdx]) {
			FREE_BDD(gr1_star_mem.fulfill_exist_mem[existGarIdx][c_fulfill_tmp]);
			c_fulfill_tmp++;
		}
		//store current number of iterations
		cfulfill_exist_mem[existGarIdx] = c_fulfill;
	}


	DdNode *zStatesStartingSfaWords = Cudd_bddAndAbstract(manager, exist_gars_list.sfaIniList[existGarIdx],
		lengthKSfaWordSuffix, exist_gars_list.sfaUnprimeStateVars[existGarIdx]);
	Cudd_Ref(zStatesStartingSfaWords);
	FREE_BDD(lengthKSfaWordSuffix);

	DdNode *zStatesStartingTrueStarSfaWords = Cudd_Not(Cudd_ReadOne(manager));
	Cudd_Ref(zStatesStartingTrueStarSfaWords);

	DdNode *zStatesStartingTrueStarSfaWordsPrev = NULL;

	while (zStatesStartingTrueStarSfaWordsPrev == NULL || !IS_BDD_EQ(zStatesStartingTrueStarSfaWords, zStatesStartingTrueStarSfaWordsPrev))
	{
		FREE_BDD(zStatesStartingTrueStarSfaWordsPrev);
		zStatesStartingTrueStarSfaWordsPrev = zStatesStartingTrueStarSfaWords;
		Cudd_Ref(zStatesStartingTrueStarSfaWordsPrev);

		tmp = pred(zStatesStartingTrueStarSfaWords, -1, sysPrimeVars, envPrimeVars,
			pairs, sysTrans, envTrans, sca);
		FREE_BDD(zStatesStartingTrueStarSfaWords);

		zStatesStartingTrueStarSfaWords = Cudd_bddAnd(manager, z, tmp);
		Cudd_Ref(zStatesStartingTrueStarSfaWords);

		FREE_BDD(tmp);
		tmp = zStatesStartingTrueStarSfaWords;

		zStatesStartingTrueStarSfaWords = Cudd_bddOr(manager, zStatesStartingSfaWords, tmp);
		Cudd_Ref(zStatesStartingTrueStarSfaWords);

		FREE_BDD(tmp);

		if (mem) {
			//store current iteration
			if (c_towards < ctowards_exist_mem[existGarIdx]) {
				FREE_BDD(gr1_star_mem.towards_exist_mem[existGarIdx][c_towards]);
			}
			gr1_star_mem.towards_exist_mem[existGarIdx][c_towards] = zStatesStartingTrueStarSfaWords;
			Cudd_Ref(gr1_star_mem.towards_exist_mem[existGarIdx][c_towards]);
			c_towards++;
			if (c_towards == *towardsCurrSize) {
				*towardsCurrSize = (*towardsCurrSize) * 2;
				extend_size_2D(gr1_star_mem.towards_exist_mem, gr1_star_mem.exist_sizeD1, *towardsCurrSize);
			}
		}
	}

	FREE_BDD(zStatesStartingTrueStarSfaWordsPrev);
	FREE_BDD(zStatesStartingSfaWords);

	if (mem) {
		//free unused, older memory values
		int c_towards_tmp = c_towards;
		while (c_towards_tmp < ctowards_exist_mem[existGarIdx]) {
			FREE_BDD(gr1_star_mem.towards_exist_mem[existGarIdx][c_towards_tmp]);
			c_towards_tmp++;
		}
		//store current number of iterations
		ctowards_exist_mem[existGarIdx] = c_towards;
	}

	return zStatesStartingTrueStarSfaWords;
}

/*Frees toPrime*/
DdNode* pred_orig(DdNode* toPrime, int existGarIdx, DdNode* sysPrimeVars, DdNode* envPrimeVars, DdNode* sysTrans, DdNode* envTrans, int sca)
{
	DdNode* modulesPrimeVars = Cudd_bddAnd(manager, sysPrimeVars, envPrimeVars);
	Cudd_Ref(modulesPrimeVars);

	DdNode* modulesTrans = Cudd_bddAnd(manager, sysTrans, envTrans);
	Cudd_Ref(modulesTrans);

	DdNode *tmp, *res;

	if (exist_gars_list.isInit && existGarIdx >= 0 && existGarIdx < exist_gars_list.listSize) {
		tmp = Cudd_bddAnd(manager, modulesTrans, exist_gars_list.sfaTransList[existGarIdx]);
		Cudd_Ref(tmp);
		FREE_BDD(modulesTrans);
		modulesTrans = tmp;
	}

	if (sca) {
		res = Cudd_bddAndAbstract(manager, modulesTrans, toPrime, modulesPrimeVars);
		Cudd_Ref(res);
	}
	else {
		tmp = Cudd_bddAnd(manager, modulesTrans, toPrime);
		Cudd_Ref(tmp);
		res = Cudd_bddExistAbstract(manager, tmp, modulesPrimeVars);
		Cudd_Ref(res);
		FREE_BDD(tmp);
	}

	FREE_BDD(modulesTrans);
	FREE_BDD(modulesPrimeVars);
	FREE_BDD(toPrime);

	return res;
}

DdNode* pred(DdNode* to, int existGarIdx, DdNode* sysPrimeVars, DdNode* envPrimeVars,
	CuddPairing* pairs, DdNode* sysTrans, DdNode* envTrans, int sca)
{
	int n;
	unsigned int *arr;
	DdNode *res, *tmp;

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
	
	res = Cudd_bddPermute(manager, to, arr); //Prime(to)
	Cudd_Ref(res);
	free(arr);

	if (!sys_trans_quant_list.isInit || !env_trans_quant_list.isInit) {
		return pred_orig(res, existGarIdx, sysPrimeVars, envPrimeVars, sysTrans, envTrans, sca);
	}

	if(exist_gars_list.isInit && existGarIdx >= 0 && existGarIdx < exist_gars_list.listSize) {
		if (sca) {
			tmp = Cudd_bddAndAbstract(manager, res, exist_gars_list.sfaTransList[existGarIdx], exist_gars_list.sfaPrimedStateVars[existGarIdx]);
			Cudd_Ref(tmp);
			FREE_BDD(res);
			res = tmp;
		}
		else {
			tmp = Cudd_bddAnd(manager, res, exist_gars_list.sfaTransList[existGarIdx]);
			Cudd_Ref(tmp);
			FREE_BDD(res);
			res = Cudd_bddExistAbstract(manager, tmp, exist_gars_list.sfaPrimedStateVars[existGarIdx]);
			Cudd_Ref(res);
			FREE_BDD(tmp);
		}
	}

	for (int i = 0; i < sys_trans_quant_list.listSize; i++) {
		if (sca) {
			tmp = Cudd_bddAndAbstract(manager, res, sys_trans_quant_list.transList[i], sys_trans_quant_list.quantSets[i]);
			Cudd_Ref(tmp);
			FREE_BDD(res);
			res = tmp;
		}
		else {
			tmp = Cudd_bddAnd(manager, res, sys_trans_quant_list.transList[i]);
			Cudd_Ref(tmp);
			FREE_BDD(res);
			res = Cudd_bddExistAbstract(manager, tmp, sys_trans_quant_list.quantSets[i]);
			Cudd_Ref(res);
			FREE_BDD(tmp);
		}
	}

	for (int i = 0; i < env_trans_quant_list.listSize; i++) {
		if (sca) {
			tmp = Cudd_bddAndAbstract(manager, res, env_trans_quant_list.transList[i], env_trans_quant_list.quantSets[i]);
			Cudd_Ref(tmp);
			FREE_BDD(res);
			res = tmp;
		}
		else {
			tmp = Cudd_bddAnd(manager, res, env_trans_quant_list.transList[i]);
			Cudd_Ref(tmp);
			FREE_BDD(res);
			res = Cudd_bddExistAbstract(manager, tmp, env_trans_quant_list.quantSets[i]);
			Cudd_Ref(res);
			FREE_BDD(tmp);
		}
	}

	return res;
}

int gr1_star_game(DdNode** sysJ, int sysJSize, DdNode** envJ, int envJSize, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans,
	DdNode* sysUnprime, DdNode* envUnprime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
	int efp, int eun, int fpr, int sca, int mem)
{
	int justiceIterCurrSize = 50, fulfillExistIterCurrSize = 50, vIsNonEmpty,
		towardsExistIterCurrSize = 50, jViolationIterCurrSize = 50, firstZIter = true, *cy_mem = NULL, cfulfill_exist_mem = NULL, *ctowards_exist_mem = NULL, eunDetected = false;
	DdNode *z, *zPrev, *zNext, *V, *tmp, *existK, *gr1;
	
	if (mem) {
		init_memory(justiceIterCurrSize, fulfillExistIterCurrSize, towardsExistIterCurrSize, jViolationIterCurrSize, sysJSize, envJSize);
		cy_mem = malloc(sysJSize * sizeof(int));
		memset(cy_mem, -1, sysJSize * sizeof(int));

		//initialize mappings of each exist. gar to the number of fixed-point iterations
		cfulfill_exist_mem = malloc(gr1_star_mem.exist_sizeD1 * sizeof(int));
		ctowards_exist_mem = malloc(gr1_star_mem.exist_sizeD1 * sizeof(int));

		memset(cfulfill_exist_mem, -1, gr1_star_mem.exist_sizeD1 * sizeof(int));
		memset(ctowards_exist_mem, -1, gr1_star_mem.exist_sizeD1 * sizeof(int));
	}

	if (exist_gars_list.isInit) {
		V = compute_env_assumption_violation(envJ, &jViolationIterCurrSize, envJSize, sysTrans,
			envTrans, sysPrimeVars, envPrimeVars, pairs, sca, mem);
		tmp = Cudd_Not(Cudd_ReadOne(manager));
		Cudd_Ref(tmp);
		if (IS_BDD_EQ(V, tmp)) { //V is an empty set
			vIsNonEmpty = false;
			if (mem) {
				for (int i = 0; i < gr1_star_mem.x_sizeD2; i++) {
					for (int cy = 0; cy < gr1_star_mem.envJ_violation_sizeD2; cy++) {
						FREE_BDD(gr1_star_mem.envJ_violation_mem[i][cy]);
					}
					free(gr1_star_mem.envJ_violation_mem[i]);
				}
				free(gr1_star_mem.envJ_violation_mem);
				gr1_star_mem.envJ_violation_mem = NULL;
				gr1_star_mem.envJ_violation_sizeD2 = 0;
			}
			FREE_BDD(V);
		}
		else {
			vIsNonEmpty = true;
		}
		FREE_BDD(tmp);
	}

	z = Cudd_ReadOne(manager);
	Cudd_Ref(z);
	zPrev = NULL;
	while (zPrev == NULL || !IS_BDD_EQ(z, zPrev))
	{ 
		FREE_BDD(zPrev);
		zPrev = z;
		Cudd_Ref(zPrev);
		
		zNext = Cudd_ReadOne(manager);
		Cudd_Ref(zNext);

		for (int k = 0; exist_gars_list.isInit && k < exist_gars_list.listSize; k++) {
			existK = compute_exist_iteration(z, k, &fulfillExistIterCurrSize, &towardsExistIterCurrSize, sysJ, sysJSize,
				envJ, envJSize, sysTrans, envTrans, sysPrimeVars, envPrimeVars, pairs,
				sca, mem, ctowards_exist_mem, cfulfill_exist_mem);
			tmp = Cudd_bddAnd(manager, zNext, existK);
			Cudd_Ref(tmp);
			FREE_BDD(zNext);
			FREE_BDD(existK);
			zNext = tmp;
		}
		
		gr1 = compute_justice_iteration(z, firstZIter, &justiceIterCurrSize, sysJ, sysJSize,
			envJ, envJSize, sysTrans, envTrans,
			sysPrimeVars, envPrimeVars, pairs,
			efp, fpr, sca, mem, cy_mem);
		
		tmp = Cudd_bddAnd(manager, zNext, gr1);
		Cudd_Ref(tmp);
		FREE_BDD(zNext);
		FREE_BDD(gr1);
		zNext = tmp;

		if (exist_gars_list.isInit && vIsNonEmpty) {
			tmp = Cudd_bddOr(manager, zNext, V);
			Cudd_Ref(tmp);
			FREE_BDD(zNext);
			zNext = tmp;
		}

		FREE_BDD(z);
		z = zNext;
		firstZIter = false;
		if (eun && !IS_BDD_EQ(z, zPrev) && !sysWinAllInitial(z, sysIni, envIni, sysUnprime, envUnprime)) {
			//printf("sysWinAllInitial is false - detected early unrealizable\n");
			//We stop before we have reached a fixed-point, thus z is an over-approximization of the winning region
			FREE_BDD(z);
			z = Cudd_Not(Cudd_ReadOne(manager));
			Cudd_Ref(z);
			eunDetected = true;
			break;
		}
	}

	FREE_BDD(zPrev);

	if (exist_gars_list.isInit && vIsNonEmpty) {
		FREE_BDD(V);
	}

	if (mem) {
		gr1_star_mem.x_sizeD3 = malloc(sysJSize * sizeof(int));
		memcpy(gr1_star_mem.x_sizeD3, cy_mem, sysJSize * sizeof(int));
		free(cy_mem);
		cy_mem = NULL;

		gr1_star_mem.fulfill_exist_sizeD2 = malloc(gr1_star_mem.exist_sizeD1 * sizeof(int));
		memcpy(gr1_star_mem.fulfill_exist_sizeD2, cfulfill_exist_mem, gr1_star_mem.exist_sizeD1 * sizeof(int));
		free(cfulfill_exist_mem);
		cfulfill_exist_mem = NULL;

		gr1_star_mem.towards_exist_sizeD2 = malloc(gr1_star_mem.exist_sizeD1 * sizeof(int));
		memcpy(gr1_star_mem.towards_exist_sizeD2, ctowards_exist_mem, gr1_star_mem.exist_sizeD1 * sizeof(int));
		free(ctowards_exist_mem);
		ctowards_exist_mem = NULL;
	}
	gr1_star_mem.sys_win = z;
	if (eunDetected) {
		return false;
	}
	return sysWinAllInitial(z, sysIni, envIni, sysUnprime, envUnprime);
}

//int gr1_star_game_1(DdNode** sysJ, int sysJSize, DdNode** envJ, int envJSize, DdNode* sysIni, DdNode* envIni, DdNode* sysTrans, DdNode* envTrans,
//	DdNode* sysUnprime, DdNode* envUnprime, DdNode* sysPrimeVars, DdNode* envPrimeVars, CuddPairing* pairs,
//	int efp, int eun, int fpr, int sca)
//{
//	//printf("\n----Start GR1 Game: efp=%d, eun=%d, fpr=%d----\n", efp, eun, fpr);
//	//printf("sysJSize=%d, envJSize=%d\n", sysJSize, envJSize);
//	gr1_star_mem.x_y_z_sizeD1 = sysJSize;
//	gr1_star_mem.x_sizeD2 = envJSize;
//
//	int currSize = 50;
//	gr1_star_mem.x_mem = malloc(sysJSize * sizeof(DdNode***));
//	gr1_star_mem.y_mem = malloc(sysJSize * sizeof(DdNode**));
//	gr1_star_mem.z_mem = malloc(sysJSize * sizeof(DdNode*));
//	for (int sysJi = 0; sysJi < sysJSize; sysJi++)
//	{
//		gr1_star_mem.x_mem[sysJi] = malloc(envJSize * sizeof(DdNode**));
//		for (int envJi = 0; envJi < envJSize; envJi++)
//		{
//			gr1_star_mem.x_mem[sysJi][envJi] = malloc(currSize * sizeof(DdNode*));
//		}
//		gr1_star_mem.y_mem[sysJi] = malloc(currSize * sizeof(DdNode*));
//	}
//
//	//gr1_star_mem.z_mem_first_itr = NULL;
//	
//
//	DdNode *x = NULL, *y, *z;
//	DdNode *xPrev, *yPrev, *zPrev;
//
//	int * cy_mem = malloc(sysJSize * sizeof(int));
//	memset(cy_mem, -1, sysJSize * sizeof(int));
//	int cy = 0; // count y
//	int firstZIter = true;
//
//	//First - Z fixed point
//	z = Cudd_ReadOne(manager);
//	Cudd_Ref(Cudd_Regular(z));
//	zPrev = NULL;
//	yPrev = NULL;
//	int j_start_idx = 0;
//
//	////printf("Z loop - before\n");
//	//Cudd_DebugCheck(manager);
//	//Cudd_CheckKeys(manager);
//
//	int zIters = 0;
//	int yIters = 0;
//	int xIters = 0;
//
//	int xtmp = 0;
//	int ytmp = 0;
//
//	int isFinished = false;
//
//
//	while (zPrev == NULL || !IS_BDD_EQ(z, zPrev))
//	{
//		zIters++;
//
//		//if (zPrev == NULL) //printf("zPrev is NULL\n");
//		//if (zPrev != NULL) //printf("IS_BDD_EQ(z, zPrev) = %d\n", IS_BDD_EQ(z, zPrev));
//
//		FREE_BDD(zPrev);
//		zPrev = z;
//		Cudd_Ref(zPrev);
//
//		for (int j = j_start_idx; j < sysJSize; j++)
//		{
//			//printf("Z loop %d: j = %d\n", zIters, j); 
//			//fflush(stdout);
//			//Cudd_DebugCheck(manager);
//			//Cudd_CheckKeys(manager);
//
//			cy = 0;
//			y = Cudd_Not(Cudd_ReadOne(manager));
//			Cudd_Ref(y);
//
//			FREE_BDD(yPrev);
//			DdNode* yieldStatesZ = yield(z, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
//			DdNode* yieldStatesZToJ = Cudd_bddAnd(manager, sysJ[j], yieldStatesZ);
//			Cudd_Ref(yieldStatesZToJ);
//			FREE_BDD(yieldStatesZ);
//			
//			yPrev = NULL;
//			//Second - Y fixed point 
//			while (yPrev == NULL || !IS_BDD_EQ(y, yPrev))
//			{
//				yIters++;
//				ytmp++;
//				////printf("y iterations = %d\, isFalse = %d \n", ytmp, y == Cudd_Not(Cudd_ReadOne(manager))); fflush(stdout);
//				////printf("Y loop - start\n"); fflush(stdout);
//				//Cudd_DebugCheck(manager);
//				//Cudd_CheckKeys(manager);
//
//				FREE_BDD(yPrev);
//				yPrev = y;
//				Cudd_Ref(yPrev);
//
//				////printf("Y loop - before yieldStatesY \n"); fflush(stdout);
//				//Cudd_DebugCheck(manager);
//				//Cudd_CheckKeys(manager);
//
//				DdNode* yieldStatesY = yield(y, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
//				DdNode* start = Cudd_bddOr(manager, yieldStatesZToJ, yieldStatesY);
//				Cudd_Ref(start);
//				FREE_BDD(yieldStatesY);
//
//				////printf("Y loop - before env loop \n"); fflush(stdout);
//				//Cudd_DebugCheck(manager);
//				//Cudd_CheckKeys(manager);
//
//				FREE_BDD(y);
//				y = Cudd_Not(Cudd_ReadOne(manager));
//				Cudd_Ref(y);
//
//				for (int i = 0; i < envJSize; i++)
//				{
//					////printf("Y loop - i = %d\n", i); fflush(stdout);
//					//Cudd_DebugCheck(manager);
//					//Cudd_CheckKeys(manager);
//
//					DdNode* negEnvJ = Cudd_Not(envJ[i]);
//					Cudd_Ref(negEnvJ);
//					FREE_BDD(x);
//
//					if (fpr && !firstZIter)
//					{
//						int rcy = -1;
//						if (cy < cy_mem[j])
//						{
//							rcy = cy;
//						}
//							if (rcy == -1) {
//								x = z;
//								Cudd_Ref(x);
//							}
//							else {
//								//printf("recycleFixPoint X for j=%d, i=%d, rcy=%d\n", j, i, rcy);
//								x = Cudd_bddAnd(manager, gr1_star_mem.x_mem[j][i][rcy], z);
//								Cudd_Ref(x);
//							}
//					}
//					else {
//						x = z;
//						Cudd_Ref(x);
//					}
//
//					xPrev = NULL;
//					// Third - X fixed point
//					while (xPrev == NULL || !IS_BDD_EQ(x, xPrev))
//					{
//						xIters++;
//						xtmp++;
//						////printf("X loop - start\n"); fflush(stdout);
//						//Cudd_DebugCheck(manager);
//						//Cudd_CheckKeys(manager);
//
//						FREE_BDD(xPrev);
//						xPrev = x;
//						////printf("is x one = %d\n", x == Cudd_ReadOne(manager)); fflush(stdout);
//						////printf("is xPrev one = %d\n", xPrev == Cudd_ReadOne(manager)); fflush(stdout);
//						Cudd_Ref(xPrev);
//						DdNode* yieldStatesX = yield(x, sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans, sca);
//						DdNode* yieldStatesXnotToJ = Cudd_bddAnd(manager, yieldStatesX, negEnvJ);
//						Cudd_Ref(yieldStatesXnotToJ);
//						FREE_BDD(yieldStatesX);
//
//						FREE_BDD(x);
//						x = Cudd_bddOr(manager, yieldStatesXnotToJ, start);
//						Cudd_Ref(x);
//
//						FREE_BDD(yieldStatesXnotToJ);
//					} // End X fixed point
//					  ////printf("xtmp = %d\n", xtmp);
//					xtmp = 0;
//					FREE_BDD(xPrev);
//					FREE_BDD(negEnvJ);
//					////printf("j = %d, i = %d, cy = %d\n", j,i,cy); fflush(stdout);
//					////printf("cy = %d, cy_mem[%d] = %d\n", cy,j, cy_mem[j]); fflush(stdout);
//					if (cy < cy_mem[j]) {
//						FREE_BDD(gr1_star_mem.x_mem[j][i][cy]);
//					}
//					gr1_star_mem.x_mem[j][i][cy] = x;
//					Cudd_Ref(gr1_star_mem.x_mem[j][i][cy]);
//
//					DdNode* tmp = Cudd_bddOr(manager, y, x);
//					Cudd_Ref(tmp);
//					FREE_BDD(y);
//					y = tmp;
//
//				} // End loop over envJ
//				  ////printf("j = %d, cy = %d\n", j,cy); fflush(stdout);
//				FREE_BDD(start);
//				if (cy < cy_mem[j]) {
//					FREE_BDD(gr1_star_mem.y_mem[j][cy]);
//				}
//
//				gr1_star_mem.y_mem[j][cy] = y;
//				Cudd_Ref(gr1_star_mem.y_mem[j][cy]);
//
//				cy++;
//				// extend size of x_mem and y_mem
//				if (cy == currSize) {
//					currSize = currSize * 2;
//					extend_size_3D(gr1_star_mem.x_mem, sysJSize, envJSize, currSize);
//					extend_size_2D(gr1_star_mem.y_mem, sysJSize, currSize);
//				}
//
//				////printf("IS_BDD_EQ(y, yPrev) = %d\n", IS_BDD_EQ(y, yPrev));
//			} // End Y fixed point
//			FREE_BDD(yieldStatesZToJ);
//			FREE_BDD(z);
//			z = y;
//
//			////printf("ytmp = %d\n", ytmp);
//			ytmp = 0;
//
//			if (eun && !sysWinAllInitial(z, sysIni, envIni, sysUnprime, envUnprime)) {
//				//printf("sysWinAllInitial is false - detected early unrealizable\n");
//				z = Cudd_Not(Cudd_ReadOne(manager));
//				isFinished = true;
//				break;
//			}
//
//			if (efp && !firstZIter) {
//				////printf("firstZIter = %d\n", firstZIter);
//				if (IS_BDD_EQ(gr1_star_mem.z_mem[j], z)) {
//					//printf("detected early fixed point\n");
//					FREE_BDD(z);
//					z = gr1_star_mem.z_mem[sysJSize - 1];
//					isFinished = true;
//					break;
//				}
//			}
//
//			//TODO: for each i save the last x_mem[j][i][cy_mem[j]] 
//			cy_mem[j] = cy;
//			gr1_star_mem.z_mem[j] = z;
//			Cudd_Ref(gr1_star_mem.z_mem[j]);
//		} // End loop over sysJ
//
//		j_start_idx = 0;
//		firstZIter = false;
//		////printf("zPrev == NULL = %d\n", (zPrev == NULL));
//		////printf("IS_BDD_EQ(z, zPrev) = %d\n", IS_BDD_EQ(z, zPrev));
//		if (isFinished) break;
//
//	} // End Z fixed point
//
//	FREE_BDD(zPrev);
//	FREE_BDD(x);
//
//	// reduce size for x_mem and y_mem if needed.
//	////printf("before x_sizeD3 malloc\n");
//	gr1_star_mem.x_sizeD3 = malloc(sysJSize * sizeof(int));
//	memcpy(gr1_star_mem.x_sizeD3, cy_mem, sysJSize * sizeof(int));
//	free(cy_mem);
//	cy_mem = NULL;
//	//for (int i = 0; i < sysJSize; i++)
//	//{
//	//	//printf("x_sizeD3[%d] = %d\n", i,gr1_star_mem.x_sizeD3[i]);
//	//	//printf("cy_mem[%d] = %d\n", i, cy_mem[i]);
//	//}
//
//	//printf("z iterations = %d\n", zIters);
//	//printf("y iterations = %d\n", yIters);
//	//printf("x iterations = %d\n", xIters);
//
//	int is_real = sysWinAllInitial(z, sysIni, envIni, sysUnprime, envUnprime);
//	//printf("End GR1 Game: is realizable = %d\n", is_real);
//
//	//Cudd_DebugCheck(manager);
//	//Cudd_CheckKeys(manager);
//	//fflush(stdout);
//
//	return is_real;
//}