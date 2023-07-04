/*
*	Implementation of the the GR1 game related functions from synt.h
*/

#include "synt.h"
#include "cuddInt.h"
#include <stdio.h>

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
