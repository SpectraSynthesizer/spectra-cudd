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
*	Implementation of the general functions from synt.h
*/

#include "synt.h"

#include <time.h> 

sizeD1 = 0;
sizeD2 = 0;

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