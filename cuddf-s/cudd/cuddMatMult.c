/**
  @file

  @ingroup cudd

  @brief Matrix multiplication functions.

  @author Fabio Somenzi

  @copyright@parblock
  Copyright (c) 1995-2015, Regents of the University of Colorado

  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:

  Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

  Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

  Neither the name of the University of Colorado nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
  COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
  ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
  POSSIBILITY OF SUCH DAMAGE.
  @endparblock

*/

#include "../util/util.h"
#include "cuddInt.h"


/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/** \cond */

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static DdNode * addMMRecur (DdManager *dd, DdNode *A, DdNode *B, int topP, int *vars);
static DdNode * addTriangleRecur (DdManager *dd, DdNode *f, DdNode *g, int *vars, DdNode *cube);
static DdNode * cuddAddOuterSumRecur (DdManager *dd, DdNode *M, DdNode *r, DdNode *c);

/** \endcond */


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**
  @brief Calculates the product of two matrices represented as
  ADDs.

  @details This procedure implements the quasiring multiplication
  algorithm.  A is assumed to depend on variables x (rows) and z
  (columns).  B is assumed to depend on variables z (rows) and y
  (columns).  The product of A and B then depends on x (rows) and y
  (columns).  Only the z variables have to be explicitly identified;
  they are the "summation" variables.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

  @see Cudd_addTimesPlus Cudd_addTriangle Cudd_bddAndAbstract

*/
DdNode *
Cudd_addMatrixMultiply(
  DdManager * dd,
  DdNode * A,
  DdNode * B,
  DdNode ** z,
  int  nz)
{
    int i, nvars, *vars;
    DdNode *res; 

    /* Array vars says what variables are "summation" variables. */
    nvars = dd->size;
    vars = ALLOC(int,nvars);
    if (vars == NULL) {
	dd->errorCode = CUDD_MEMORY_OUT;
	return(NULL);
    }
    for (i = 0; i < nvars; i++) {
        vars[i] = 0;
    }
    for (i = 0; i < nz; i++) {
        vars[z[i]->index] = 1;
    }

    do {
	dd->reordered = 0;
	res = addMMRecur(dd,A,B,-1,vars);
    } while (dd->reordered == 1);
    FREE(vars);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_addMatrixMultiply */


/**
  @brief Calculates the product of two matrices represented as
  ADDs.

  @details Calculates the product of two matrices, A and B,
  represented as ADDs, using the CMU matrix by matrix multiplication
  procedure by Clarke et al..  Matrix A has x's as row variables and
  z's as column variables, while matrix B has z's as row variables and
  y's as column variables.  The resulting matrix has x's as row
  variables and y's as column variables.

  @return the pointer to the result if successful; NULL otherwise.

  @sideeffect None

  @see Cudd_addMatrixMultiply

*/
DdNode *
Cudd_addTimesPlus(
  DdManager * dd,
  DdNode * A,
  DdNode * B,
  DdNode ** z,
  int  nz)
{
    DdNode *w, *cube, *tmp, *res; 
    int i;
    tmp = Cudd_addApply(dd,Cudd_addTimes,A,B);
    if (tmp == NULL) return(NULL);
    Cudd_Ref(tmp);
    Cudd_Ref(cube = DD_ONE(dd));
    for (i = nz-1; i >= 0; i--) {
	 w = Cudd_addIte(dd,z[i],cube,DD_ZERO(dd));
	 if (w == NULL) {
	    Cudd_RecursiveDeref(dd,tmp);
	    return(NULL);
	 }
	 Cudd_Ref(w);
	 Cudd_RecursiveDeref(dd,cube);
	 cube = w;
    }
    res = Cudd_addExistAbstract(dd,tmp,cube);
    if (res == NULL) {
	Cudd_RecursiveDeref(dd,tmp);
	Cudd_RecursiveDeref(dd,cube);
	return(NULL);
    }
    Cudd_Ref(res);
    Cudd_RecursiveDeref(dd,cube);
    Cudd_RecursiveDeref(dd,tmp);
    Cudd_Deref(res);
    return(res);

} /* end of Cudd_addTimesPlus */


/**
  @brief Performs the triangulation step for the shortest path
  computation.

  @details Implements the semiring multiplication algorithm used in
  the triangulation step for the shortest path computation.  f
  is assumed to depend on variables x (rows) and z (columns).  g is
  assumed to depend on variables z (rows) and y (columns).  The product
  of f and g then depends on x (rows) and y (columns).  Only the z
  variables have to be explicitly identified; they are the
  "abstraction" variables.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

  @see Cudd_addMatrixMultiply Cudd_bddAndAbstract

*/
DdNode *
Cudd_addTriangle(
  DdManager * dd,
  DdNode * f,
  DdNode * g,
  DdNode ** z,
  int  nz)
{
    int    i, nvars, *vars;
    DdNode *res, *cube;

    nvars = dd->size;
    vars = ALLOC(int, nvars);
    if (vars == NULL) {
	dd->errorCode = CUDD_MEMORY_OUT;
	return(NULL);
    }
    for (i = 0; i < nvars; i++) vars[i] = -1;
    for (i = 0; i < nz; i++) vars[z[i]->index] = i;
    cube = Cudd_addComputeCube(dd, z, NULL, nz);
    if (cube == NULL) {
	FREE(vars);
	return(NULL);
    }
    cuddRef(cube);

    do {
	dd->reordered = 0;
	res = addTriangleRecur(dd, f, g, vars, cube);
    } while (dd->reordered == 1);
    if (res != NULL) cuddRef(res);
    Cudd_RecursiveDeref(dd,cube);
    if (res != NULL) cuddDeref(res);
    FREE(vars);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_addTriangle */


/**
  @brief Takes the minimum of a matrix and the outer sum of two vectors.

  @details Takes the pointwise minimum of a matrix and the outer
  sum of two vectors.  This procedure is used in the Floyd-Warshall
  all-pair shortest path algorithm.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

*/
DdNode *
Cudd_addOuterSum(
  DdManager *dd,
  DdNode *M,
  DdNode *r,
  DdNode *c)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = cuddAddOuterSumRecur(dd, M, r, c);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);

} /* end of Cudd_addOuterSum */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**
  @brief Performs the recursive step of Cudd_addMatrixMultiply.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

*/
static DdNode *
addMMRecur(
  DdManager * dd,
  DdNode * A,
  DdNode * B,
  int  topP,
  int * vars)
{
    DdNode *zero,
           *At,		/* positive cofactor of first operand */
	   *Ae,		/* negative cofactor of first operand */
	   *Bt,		/* positive cofactor of second operand */
	   *Be,		/* negative cofactor of second operand */
	   *t,		/* positive cofactor of result */
	   *e,		/* negative cofactor of result */
	   *scaled,	/* scaled result */
	   *add_scale,	/* ADD representing the scaling factor */
	   *res;
    int	i;		/* loop index */
    double scale;	/* scaling factor */
    int index;		/* index of the top variable */
    CUDD_VALUE_TYPE value;
    int topA, topB, topV;
    DD_CTFP cacheOp;

    statLine(dd);
    zero = DD_ZERO(dd);

    if (A == zero || B == zero) {
        return(zero);
    }

    if (cuddIsConstant(A) && cuddIsConstant(B)) {
	/* Compute the scaling factor. It is 2^k, where k is the
	** number of summation variables below the current variable.
	** Indeed, these constants represent blocks of 2^k identical
	** constant values in both A and B.
	*/
	value = cuddV(A) * cuddV(B);
	for (i = 0; i < dd->size; i++) {
	    if (vars[i]) {
		if (dd->perm[i] > topP) {
		    value *= (CUDD_VALUE_TYPE) 2;
		}
	    }
	}
	res = cuddUniqueConst(dd, value);
	return(res);
    }

    /* Standardize to increase cache efficiency. Clearly, A*B != B*A
    ** in matrix multiplication. However, which matrix is which is
    ** determined by the variables appearing in the ADDs and not by
    ** which one is passed as first argument.
    */
    if (A > B) {
	DdNode *tmp = A;
	A = B;
	B = tmp;
    }

    topA = cuddI(dd,A->index); topB = cuddI(dd,B->index);
    topV = ddMin(topA,topB);

    cacheOp = (DD_CTFP) addMMRecur;
    res = cuddCacheLookup2(dd,cacheOp,A,B);
    if (res != NULL) {
	/* If the result is 0, there is no need to normalize.
	** Otherwise we count the number of z variables between
	** the current depth and the top of the ADDs. These are
	** the missing variables that determine the size of the
	** constant blocks.
	*/
	if (res == zero) return(res);
	scale = 1.0;
	for (i = 0; i < dd->size; i++) {
	    if (vars[i]) {
		if (dd->perm[i] > topP && dd->perm[i] < topV) {
		    scale *= 2;
		}
	    }
	}
	if (scale > 1.0) {
	    cuddRef(res);
	    add_scale = cuddUniqueConst(dd,(CUDD_VALUE_TYPE)scale);
	    if (add_scale == NULL) {
		Cudd_RecursiveDeref(dd, res);
		return(NULL);
	    }
	    cuddRef(add_scale);
	    scaled = cuddAddApplyRecur(dd,Cudd_addTimes,res,add_scale);
	    if (scaled == NULL) {
		Cudd_RecursiveDeref(dd, add_scale);
		Cudd_RecursiveDeref(dd, res);
		return(NULL);
	    }
	    cuddRef(scaled);
	    Cudd_RecursiveDeref(dd, add_scale);
	    Cudd_RecursiveDeref(dd, res);
	    res = scaled;
	    cuddDeref(res);
	}
        return(res);
    }

    checkWhetherToGiveUp(dd);

    /* compute the cofactors */
    if (topV == topA) {
	At = cuddT(A);
	Ae = cuddE(A);
    } else {
	At = Ae = A;
    }
    if (topV == topB) {
	Bt = cuddT(B);
	Be = cuddE(B);
    } else {
	Bt = Be = B;
    }

    t = addMMRecur(dd, At, Bt, (int)topV, vars);
    if (t == NULL) return(NULL);
    cuddRef(t);
    e = addMMRecur(dd, Ae, Be, (int)topV, vars);
    if (e == NULL) {
	Cudd_RecursiveDeref(dd, t);
	return(NULL);
    }
    cuddRef(e);

    index = dd->invperm[topV];
    if (vars[index] == 0) {
	/* We have split on either the rows of A or the columns
	** of B. We just need to connect the two subresults,
	** which correspond to two submatrices of the result.
	*/
	res = (t == e) ? t : cuddUniqueInter(dd,index,t,e);
	if (res == NULL) {
	    Cudd_RecursiveDeref(dd, t);
	    Cudd_RecursiveDeref(dd, e);
	    return(NULL);
	}
	cuddRef(res);
	cuddDeref(t);
	cuddDeref(e);
    } else {
	/* we have simultaneously split on the columns of A and
	** the rows of B. The two subresults must be added.
	*/
	res = cuddAddApplyRecur(dd,Cudd_addPlus,t,e);
	if (res == NULL) {
	    Cudd_RecursiveDeref(dd, t);
	    Cudd_RecursiveDeref(dd, e);
	    return(NULL);
	}
	cuddRef(res);
	Cudd_RecursiveDeref(dd, t);
	Cudd_RecursiveDeref(dd, e);
    }

    cuddCacheInsert2(dd,cacheOp,A,B,res);

    /* We have computed (and stored in the computed table) a minimal
    ** result; that is, a result that assumes no summation variables
    ** between the current depth of the recursion and its top
    ** variable. We now take into account the z variables by properly
    ** scaling the result.
    */
    if (res != zero) {
	scale = 1.0;
	for (i = 0; i < dd->size; i++) {
	    if (vars[i]) {
		if (dd->perm[i] > topP && dd->perm[i] < topV) {
		    scale *= 2;
		}
	    }
	}
	if (scale > 1.0) {
	    add_scale = cuddUniqueConst(dd,(CUDD_VALUE_TYPE)scale);
	    if (add_scale == NULL) {
		Cudd_RecursiveDeref(dd, res);
		return(NULL);
	    }
	    cuddRef(add_scale);
	    scaled = cuddAddApplyRecur(dd,Cudd_addTimes,res,add_scale);
	    if (scaled == NULL) {
		Cudd_RecursiveDeref(dd, res);
		Cudd_RecursiveDeref(dd, add_scale);
		return(NULL);
	    }
	    cuddRef(scaled);
	    Cudd_RecursiveDeref(dd, add_scale);
	    Cudd_RecursiveDeref(dd, res);
	    res = scaled;
	}
    }
    cuddDeref(res);
    return(res);

} /* end of addMMRecur */


/**
  @brief Performs the recursive step of Cudd_addTriangle.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

*/
static DdNode *
addTriangleRecur(
  DdManager * dd,
  DdNode * f,
  DdNode * g,
  int * vars,
  DdNode *cube)
{
    DdNode *fv, *fvn, *gv, *gvn, *t, *e, *res;
    CUDD_VALUE_TYPE value;
    int top, topf, topg, index;

    statLine(dd);
    if (f == DD_PLUS_INFINITY(dd) || g == DD_PLUS_INFINITY(dd)) {
	return(DD_PLUS_INFINITY(dd));
    }

    if (cuddIsConstant(f) && cuddIsConstant(g)) {
	value = cuddV(f) + cuddV(g);
	res = cuddUniqueConst(dd, value);
	return(res);
    }
    if (f < g) {
	DdNode *tmp = f;
	f = g;
	g = tmp;
    }

    if (f->ref != 1 || g->ref != 1) {
	res = cuddCacheLookup(dd, DD_ADD_TRIANGLE_TAG, f, g, cube);
	if (res != NULL) {
	    return(res);
	}
    }

    checkWhetherToGiveUp(dd);

    topf = cuddI(dd,f->index); topg = cuddI(dd,g->index);
    top = ddMin(topf,topg);

    if (top == topf) {fv = cuddT(f); fvn = cuddE(f);} else {fv = fvn = f;}
    if (top == topg) {gv = cuddT(g); gvn = cuddE(g);} else {gv = gvn = g;}

    t = addTriangleRecur(dd, fv, gv, vars, cube);
    if (t == NULL) return(NULL);
    cuddRef(t);
    e = addTriangleRecur(dd, fvn, gvn, vars, cube);
    if (e == NULL) {
	Cudd_RecursiveDeref(dd, t);
	return(NULL);
    }
    cuddRef(e);

    index = dd->invperm[top];
    if (vars[index] < 0) {
	res = (t == e) ? t : cuddUniqueInter(dd,index,t,e);
	if (res == NULL) {
	    Cudd_RecursiveDeref(dd, t);
	    Cudd_RecursiveDeref(dd, e);
	    return(NULL);
	}
	cuddDeref(t);
	cuddDeref(e);
    } else {
	res = cuddAddApplyRecur(dd,Cudd_addMinimum,t,e);
	if (res == NULL) {
	    Cudd_RecursiveDeref(dd, t);
	    Cudd_RecursiveDeref(dd, e);
	    return(NULL);
	}
	cuddRef(res);
	Cudd_RecursiveDeref(dd, t);
	Cudd_RecursiveDeref(dd, e);
	cuddDeref(res);
    }

    if (f->ref != 1 || g->ref != 1) {
	cuddCacheInsert(dd, DD_ADD_TRIANGLE_TAG, f, g, cube, res);
    }

    return(res);

} /* end of addTriangleRecur */


/**
  @brief Performs the recursive step of Cudd_addOuterSum.

  @return a pointer to the result if successful; NULL otherwise.

  @sideeffect None

*/
static DdNode *
cuddAddOuterSumRecur(
  DdManager *dd,
  DdNode *M,
  DdNode *r,
  DdNode *c)
{
    DdNode *P, *R, *Mt, *Me, *rt, *re, *ct, *ce, *Rt, *Re;
    int topM, topc, topr;
    int v, index;

    statLine(dd);
    /* Check special cases. */
    if (r == DD_PLUS_INFINITY(dd) || c == DD_PLUS_INFINITY(dd)) return(M); 

    if (cuddIsConstant(c) && cuddIsConstant(r)) {
	R = cuddUniqueConst(dd,Cudd_V(c)+Cudd_V(r));
	cuddRef(R);
	if (cuddIsConstant(M)) {
	    if (cuddV(R) <= cuddV(M)) {
		cuddDeref(R);
	        return(R);
	    } else {
	        Cudd_RecursiveDeref(dd,R);       
		return(M);
	    }
	} else {
	    P = Cudd_addApply(dd,Cudd_addMinimum,R,M);
	    cuddRef(P);
	    Cudd_RecursiveDeref(dd,R);
	    cuddDeref(P);
	    return(P);
	}
    }

    /* Check the cache. */
    R = cuddCacheLookup(dd,DD_ADD_OUT_SUM_TAG,M,r,c);
    if (R != NULL) return(R);

    checkWhetherToGiveUp(dd);

    topM = cuddI(dd,M->index); topr = cuddI(dd,r->index);
    topc = cuddI(dd,c->index);
    v = ddMin(topM,ddMin(topr,topc));

    /* Compute cofactors. */
    if (topM == v) { Mt = cuddT(M); Me = cuddE(M); } else { Mt = Me = M; }
    if (topr == v) { rt = cuddT(r); re = cuddE(r); } else { rt = re = r; }
    if (topc == v) { ct = cuddT(c); ce = cuddE(c); } else { ct = ce = c; }

    /* Recursively solve. */
    Rt = cuddAddOuterSumRecur(dd,Mt,rt,ct);
    if (Rt == NULL) return(NULL);
    cuddRef(Rt);
    Re = cuddAddOuterSumRecur(dd,Me,re,ce);
    if (Re == NULL) {
	Cudd_RecursiveDeref(dd, Rt);
	return(NULL);
    }
    cuddRef(Re);
    index = dd->invperm[v];
    R = (Rt == Re) ? Rt : cuddUniqueInter(dd,index,Rt,Re);
    if (R == NULL) {
	Cudd_RecursiveDeref(dd, Rt);
	Cudd_RecursiveDeref(dd, Re);
	return(NULL);
    }
    cuddDeref(Rt);
    cuddDeref(Re);

    /* Store the result in the cache. */
    cuddCacheInsert(dd,DD_ADD_OUT_SUM_TAG,M,r,c,R);

    return(R);

} /* end of cuddAddOuterSumRecur */


unsigned char
Cudd_addBellmanFord(
	DdManager * dd,
	DdNode * A, /*weighted graph\arena*/
	DdNode * S, /*Source states*/
	DdNode * primedVars, /*both modules primed variabels*/
	DdNode ** primedUnprimedPairing /*the ith index is mapped to the other version of the ith variable*/
)
{
	int *unprimedVarsIdx, *primedVarsIdx, i, j, size;
	DdNode **newVarsArr;
	DdNode **primedVarsArr, **unPrimedVarsArr;
	DdNode *curS, *curA, *prevS, *newVarsCube, *curSUtil, *curSUtil_1, *curSUtil_2;
	unsigned long long V, n, k; /*number of states*/
	unsigned char neg_cycle;


	/*get the indices of all primed variables*/
	primedVarsIdx = Cudd_SupportIndex(dd, primedVars);

	/*count the number of primed/unprimed vars*/
	n = 0;
	for (i = 0; i < dd->size; i++) {
		if (primedVarsIdx[i] > 0) {
			n++;
		}
	}

	newVarsArr = (DdNode**)malloc(sizeof(DdNode*)*n);
	if (newVarsArr == NULL) {
		return NULL;
	}
	primedVarsArr = (DdNode**)malloc(sizeof(DdNode*)*n);
	if (primedVarsArr == NULL) {
		free(newVarsArr);
		return NULL;
	}
	unPrimedVarsArr = (DdNode**)malloc(sizeof(DdNode*)*n);
	if (unPrimedVarsArr == NULL) {
		free(newVarsArr);
		free(primedVarsArr);
		return NULL;
	}
	size = dd->size;
	for (i = 0, j = 0; i < size; i++) {
		printf("i == %d\n", i);
		if (primedVarsIdx[i] > 0) { // the ith variable is a primed var
			printf("a primed variable found...i == %d\n", i);
			newVarsArr[j] = Cudd_addNewVar(dd);
			primedVarsArr[j] = Cudd_addIthVar(dd, i);
			if (newVarsArr[j] == NULL || primedVarsArr[j] == NULL) {
				free(newVarsArr);
				free(primedVarsArr);
				free(unPrimedVarsArr);
				return NULL;
			}
			Cudd_Ref(newVarsArr[j]);
			Cudd_Ref(primedVarsArr[j]);
			unPrimedVarsArr[j] = Cudd_addIthVar(dd, primedUnprimedPairing[i]->index); //map the unprimed version of the ith variable to the same new var
			Cudd_Ref(unPrimedVarsArr[j]);
			printf("%s %d , i == %d \n", "unprimed index", unPrimedVarsArr[j]->index, i);
			j++;
		}
	}

	printf("going to swap vars...\n");
	curA = Cudd_addSwapVariables(dd, A, unPrimedVarsArr, newVarsArr, n);
	printf("swap vars finished\n");
	Cudd_Ref(curA);
	printf("n == %d\n", n);
	V = 1;
	V <<= 2 * n;
	printf("V = %llu\n", V);
	neg_cycle = 1;
	curS = S;
	prevS = NULL;
	//printf("original A:\n");
	//cuddP(dd, A);
	Cudd_Ref(curS);
	//Cudd_Ref(curS);
	printf("curS:\n");
	//cuddP(dd, curS);
	//printf("curA:\n");
	//cuddP(dd, curA);
	for (k = 0; k <= V; k++) {
		if (curS == prevS) {
			printf("neg cycle not found\n");
			neg_cycle = 0;
			break;
		}
		if (prevS != NULL) {
			Cudd_RecursiveDeref(dd, prevS);
		}
		prevS = curS;
		curSUtil_1 = Cudd_addSwapVariables(dd, prevS, primedVarsArr, newVarsArr, n);
		//curSUtil_2 = Cudd_addSwapVariables(dd, prevS, unPrimedVarsArr, newVarsArr, n);
		Cudd_Ref(curSUtil_1);
		//Cudd_Ref(curSUtil_2);
		curS = Cudd_addTriangle(dd, curSUtil_1, curA, newVarsArr, n);
		Cudd_Ref(curS);
		printf("i == %d, curS:\n", k);
		//cuddP(dd, curS);
		Cudd_RecursiveDeref(dd, curSUtil_1);
		//Cudd_RecursiveDeref(dd, curSUtil_2);
		curSUtil = Cudd_addApply(dd, Cudd_addMinimum, curS, prevS);
		Cudd_Ref(curSUtil);
		Cudd_RecursiveDeref(dd, curS);
		curS = curSUtil;
	}
	//cuddP(dd, curS);
	Cudd_RecursiveDeref(dd, prevS);
	Cudd_RecursiveDeref(dd, curS);
	free(newVarsArr);
	free(primedVarsArr);
	free(unPrimedVarsArr);
	return neg_cycle;
}