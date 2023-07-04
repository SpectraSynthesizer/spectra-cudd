/**
  @file

  @ingroup cudd

  @brief Quantification functions for BDDs.

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

static int bddCheckPositiveCube (DdManager *manager, DdNode *cube);

/** \endcond */


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**
  @brief Existentially abstracts all the variables in cube from f.

  @return the abstracted %BDD if successful; NULL otherwise.

  @sideeffect None

  @see Cudd_bddUnivAbstract Cudd_addExistAbstract

*/
DdNode *
Cudd_bddExistAbstract(
  DdManager * manager,
  DdNode * f,
  DdNode * cube)
{
    DdNode *res;

    if (bddCheckPositiveCube(manager, cube) == 0) {
        (void) fprintf(manager->err,
		       "Error: Can only abstract positive cubes\n");
	manager->errorCode = CUDD_INVALID_ARG;
        return(NULL);
    }

    do {
	manager->reordered = 0;
	res = cuddBddExistAbstractRecur(manager, f, cube);
    } while (manager->reordered == 1);
    if (manager->errorCode == CUDD_TIMEOUT_EXPIRED && manager->timeoutHandler) {
        manager->timeoutHandler(manager, manager->tohArg);
    }

    return(res);

} /* end of Cudd_bddExistAbstract */


/**
  @brief Existentially abstracts all the variables in cube from f.

  @return the abstracted %BDD if successful; NULL if the intermediate
  result blows up or more new nodes than <code>limit</code> are
  required.

  @sideeffect None

  @see Cudd_bddExistAbstract

*/
DdNode *
Cudd_bddExistAbstractLimit(
  DdManager * manager,
  DdNode * f,
  DdNode * cube,
  unsigned int limit)
{
    DdNode *res;
    unsigned int saveLimit = manager->maxLive;

    if (bddCheckPositiveCube(manager, cube) == 0) {
        (void) fprintf(manager->err,
		       "Error: Can only abstract positive cubes\n");
	manager->errorCode = CUDD_INVALID_ARG;
        return(NULL);
    }

    manager->maxLive = (manager->keys - manager->dead) + 
        (manager->keysZ - manager->deadZ) + limit;
    do {
	manager->reordered = 0;
	res = cuddBddExistAbstractRecur(manager, f, cube);
    } while (manager->reordered == 1);
    manager->maxLive = saveLimit;
    if (manager->errorCode == CUDD_TIMEOUT_EXPIRED && manager->timeoutHandler) {
        manager->timeoutHandler(manager, manager->tohArg);
    }

    return(res);

} /* end of Cudd_bddExistAbstractLimit */


/**
  @brief Takes the exclusive OR of two BDDs and simultaneously abstracts the
  variables in cube.

  @details The variables are existentially abstracted.

  @return a pointer to the result is successful; NULL otherwise.

  @sideeffect None

  @see Cudd_bddUnivAbstract Cudd_bddExistAbstract Cudd_bddAndAbstract

*/
DdNode *
Cudd_bddXorExistAbstract(
  DdManager * manager,
  DdNode * f,
  DdNode * g,
  DdNode * cube)
{
    DdNode *res;

    if (bddCheckPositiveCube(manager, cube) == 0) {
        (void) fprintf(manager->err,
		       "Error: Can only abstract positive cubes\n");
	manager->errorCode = CUDD_INVALID_ARG;
        return(NULL);
    }

    do {
	manager->reordered = 0;
	res = cuddBddXorExistAbstractRecur(manager, f, g, cube);
    } while (manager->reordered == 1);
    if (manager->errorCode == CUDD_TIMEOUT_EXPIRED && manager->timeoutHandler) {
        manager->timeoutHandler(manager, manager->tohArg);
    }

    return(res);

} /* end of Cudd_bddXorExistAbstract */


/**
  @brief Universally abstracts all the variables in cube from f.

  @return the abstracted %BDD if successful; NULL otherwise.

  @sideeffect None

  @see Cudd_bddExistAbstract Cudd_addUnivAbstract

*/
DdNode *
Cudd_bddUnivAbstract(
  DdManager * manager,
  DdNode * f,
  DdNode * cube)
{
    DdNode	*res;

    if (bddCheckPositiveCube(manager, cube) == 0) {
	(void) fprintf(manager->err,
		       "Error: Can only abstract positive cubes\n");
	manager->errorCode = CUDD_INVALID_ARG;
	return(NULL);
    }

    do {
	manager->reordered = 0;
	res = cuddBddExistAbstractRecur(manager, Cudd_Not(f), cube);
    } while (manager->reordered == 1);
    if (res != NULL) res = Cudd_Not(res);
    if (manager->errorCode == CUDD_TIMEOUT_EXPIRED && manager->timeoutHandler) {
        manager->timeoutHandler(manager, manager->tohArg);
    }

    return(res);

} /* end of Cudd_bddUnivAbstract */


/**
  @brief Computes the boolean difference of f with respect to x.

  @details Computes the boolean difference of f with respect to the
  variable with index x.

  @return the %BDD of the boolean difference if successful; NULL
  otherwise.

  @sideeffect None

*/
DdNode *
Cudd_bddBooleanDiff(
  DdManager * manager,
  DdNode * f,
  int  x)
{
    DdNode *res, *var;

    /* If the variable is not currently in the manager, f cannot
    ** depend on it.
    */
    if (x >= manager->size) return(Cudd_Not(DD_ONE(manager)));
    var = manager->vars[x];

    do {
	manager->reordered = 0;
	res = cuddBddBooleanDiffRecur(manager, Cudd_Regular(f), var);
    } while (manager->reordered == 1);
    if (manager->errorCode == CUDD_TIMEOUT_EXPIRED && manager->timeoutHandler) {
        manager->timeoutHandler(manager, manager->tohArg);
    }

    return(res);

} /* end of Cudd_bddBooleanDiff */


/**
  @brief Checks whether a variable is dependent on others in a
  function.

  @details No new nodes are created.

  @return 1 if the variable is dependent; 0 otherwise.

  @sideeffect None

*/
int
Cudd_bddVarIsDependent(
  DdManager *dd,		/**< manager */
  DdNode *f,			/**< function */
  DdNode *var			/**< variable */)
{
    DdNode *F, *res, *zero, *ft, *fe;
    unsigned topf, level;
    DD_CTFP cacheOp;
    int retval;

    zero = Cudd_Not(DD_ONE(dd));
    F = Cudd_Regular(f);
    if (cuddIsConstant(F)) return(f == zero);

    /* From now on f is not constant. */
    topf = (unsigned) dd->perm[F->index];
    level = (unsigned) dd->perm[var->index];

    /* Check terminal case. If topf > index of var, f does not depend on var.
    ** Therefore, var is not dependent in f. */
    if (topf > level) {
	return(0);
    }

    cacheOp = (DD_CTFP) Cudd_bddVarIsDependent;
    res = cuddCacheLookup2(dd,cacheOp,f,var);
    if (res != NULL) {
	return(res != zero);
    }

    /* Compute cofactors. */
    ft = Cudd_NotCond(cuddT(F), f != F);
    fe = Cudd_NotCond(cuddE(F), f != F);

    if (topf == level) {
	retval = Cudd_bddLeq(dd,ft,Cudd_Not(fe));
    } else {
	retval = Cudd_bddVarIsDependent(dd,ft,var) &&
	    Cudd_bddVarIsDependent(dd,fe,var);
    }

    cuddCacheInsert2(dd,cacheOp,f,var,Cudd_NotCond(zero,retval));

    return(retval);

} /* Cudd_bddVarIsDependent */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/


/**
  @brief Performs the recursive steps of Cudd_bddExistAbstract.

  @details It is also used by Cudd_bddUnivAbstract.

  @return the %BDD obtained by abstracting the variables of cube from f
  if successful; NULL otherwise.

  @sideeffect None

  @see Cudd_bddExistAbstract Cudd_bddUnivAbstract

*/
DdNode *
cuddBddExistAbstractRecur(
  DdManager * manager,
  DdNode * f,
  DdNode * cube)
{
    DdNode	*F, *T, *E, *res, *res1, *res2, *one;

    statLine(manager);
    one = DD_ONE(manager);
    F = Cudd_Regular(f);

    /* Cube is guaranteed to be a cube at this point. */	
    if (cube == one || F == one) {  
        return(f);
    }
    /* From now on, f and cube are non-constant. */

    /* Abstract a variable that does not appear in f. */
    while (manager->perm[F->index] > manager->perm[cube->index]) {
	cube = cuddT(cube);
	if (cube == one) return(f);
    }

    /* Check the cache. */
    if (F->ref != 1 && (res = cuddCacheLookup2(manager, Cudd_bddExistAbstract, f, cube)) != NULL) {
	return(res);
    }

    checkWhetherToGiveUp(manager);

    /* Compute the cofactors of f. */
    T = cuddT(F); E = cuddE(F);
    if (f != F) {
	T = Cudd_Not(T); E = Cudd_Not(E);
    }

    /* If the two indices are the same, so are their levels. */
    if (F->index == cube->index) {
	if (T == one || E == one || T == Cudd_Not(E)) {
	    return(one);
	}
	res1 = cuddBddExistAbstractRecur(manager, T, cuddT(cube));
	if (res1 == NULL) return(NULL);
	if (res1 == one) {
	    if (F->ref != 1)
		cuddCacheInsert2(manager, Cudd_bddExistAbstract, f, cube, one);
	    return(one);
	}
        cuddRef(res1);
	res2 = cuddBddExistAbstractRecur(manager, E, cuddT(cube));
	if (res2 == NULL) {
	    Cudd_IterDerefBdd(manager,res1);
	    return(NULL);
	}
        cuddRef(res2);
	res = cuddBddAndRecur(manager, Cudd_Not(res1), Cudd_Not(res2));
	if (res == NULL) {
	    Cudd_IterDerefBdd(manager, res1);
	    Cudd_IterDerefBdd(manager, res2);
	    return(NULL);
	}
	res = Cudd_Not(res);
	cuddRef(res);
	Cudd_IterDerefBdd(manager, res1);
	Cudd_IterDerefBdd(manager, res2);
	if (F->ref != 1)
	    cuddCacheInsert2(manager, Cudd_bddExistAbstract, f, cube, res);
	cuddDeref(res);
        return(res);
    } else { /* if (cuddI(manager,F->index) < cuddI(manager,cube->index)) */
	res1 = cuddBddExistAbstractRecur(manager, T, cube);
	if (res1 == NULL) return(NULL);
        cuddRef(res1);
	res2 = cuddBddExistAbstractRecur(manager, E, cube);
	if (res2 == NULL) {
	    Cudd_IterDerefBdd(manager, res1);
	    return(NULL);
	}
        cuddRef(res2);
	/* ITE takes care of possible complementation of res1 and of the
        ** case in which res1 == res2. */
	res = cuddBddIteRecur(manager, manager->vars[F->index], res1, res2);
	if (res == NULL) {
	    Cudd_IterDerefBdd(manager, res1);
	    Cudd_IterDerefBdd(manager, res2);
	    return(NULL);
	}
	cuddDeref(res1);
	cuddDeref(res2);
	if (F->ref != 1)
	    cuddCacheInsert2(manager, Cudd_bddExistAbstract, f, cube, res);
	return(res);
    }	    

} /* end of cuddBddExistAbstractRecur */


/**
  @brief Takes the exclusive OR of two BDDs and simultaneously abstracts the
  variables in cube.

  @details The variables are existentially abstracted.

  @return a pointer to the result is successful; NULL otherwise.

  @sideeffect None

  @see Cudd_bddAndAbstract

*/
DdNode *
cuddBddXorExistAbstractRecur(
  DdManager * manager,
  DdNode * f,
  DdNode * g,
  DdNode * cube)
{
    DdNode *F, *fv, *fnv, *G, *gv, *gnv;
    DdNode *one, *zero, *r, *t, *e, *Cube;
    int topf, topg, topcube, top;
    unsigned int index;

    statLine(manager);
    one = DD_ONE(manager);
    zero = Cudd_Not(one);

    /* Terminal cases. */
    if (f == g) {
	return(zero);
    }
    if (f == Cudd_Not(g)) {
	return(one);
    }
    if (cube == one) {
	return(cuddBddXorRecur(manager, f, g));
    }
    if (f == one) {
	return(cuddBddExistAbstractRecur(manager, Cudd_Not(g), cube));
    }
    if (g == one) {
	return(cuddBddExistAbstractRecur(manager, Cudd_Not(f), cube));
    }
    if (f == zero) {
	return(cuddBddExistAbstractRecur(manager, g, cube));
    }
    if (g == zero) {
	return(cuddBddExistAbstractRecur(manager, f, cube));
    }

    /* At this point f, g, and cube are not constant. */

    if (f > g) { /* Try to increase cache efficiency. */
	DdNode *tmp = f;
	f = g;
	g = tmp;
    }

    /* Check cache. */
    r = cuddCacheLookup(manager, DD_BDD_XOR_EXIST_ABSTRACT_TAG, f, g, cube);
    if (r != NULL) {
	return(r);
    }

    checkWhetherToGiveUp(manager);

    /* Here we can skip the use of cuddI, because the operands are known
    ** to be non-constant.
    */
    F = Cudd_Regular(f);
    topf = manager->perm[F->index];
    G = Cudd_Regular(g);
    topg = manager->perm[G->index];
    top = ddMin(topf, topg);
    topcube = manager->perm[cube->index];

    if (topcube < top) {
	return(cuddBddXorExistAbstractRecur(manager, f, g, cuddT(cube)));
    }
    /* Now, topcube >= top. */

    if (topf == top) {
	index = F->index;
	fv = cuddT(F);
	fnv = cuddE(F);
	if (Cudd_IsComplement(f)) {
	    fv = Cudd_Not(fv);
	    fnv = Cudd_Not(fnv);
	}
    } else {
	index = G->index;
	fv = fnv = f;
    }

    if (topg == top) {
	gv = cuddT(G);
	gnv = cuddE(G);
	if (Cudd_IsComplement(g)) {
	    gv = Cudd_Not(gv);
	    gnv = Cudd_Not(gnv);
	}
    } else {
	gv = gnv = g;
    }

    if (topcube == top) {
	Cube = cuddT(cube);
    } else {
	Cube = cube;
    }

    t = cuddBddXorExistAbstractRecur(manager, fv, gv, Cube);
    if (t == NULL) return(NULL);

    /* Special case: 1 OR anything = 1. Hence, no need to compute
    ** the else branch if t is 1.
    */
    if (t == one && topcube == top) {
	cuddCacheInsert(manager, DD_BDD_XOR_EXIST_ABSTRACT_TAG, f, g, cube, one);
	return(one);
    }
    cuddRef(t);

    e = cuddBddXorExistAbstractRecur(manager, fnv, gnv, Cube);
    if (e == NULL) {
	Cudd_IterDerefBdd(manager, t);
	return(NULL);
    }
    cuddRef(e);

    if (topcube == top) {	/* abstract */
	r = cuddBddAndRecur(manager, Cudd_Not(t), Cudd_Not(e));
	if (r == NULL) {
	    Cudd_IterDerefBdd(manager, t);
	    Cudd_IterDerefBdd(manager, e);
	    return(NULL);
	}
	r = Cudd_Not(r);
	cuddRef(r);
	Cudd_IterDerefBdd(manager, t);
	Cudd_IterDerefBdd(manager, e);
	cuddDeref(r);
    } else if (t == e) {
	r = t;
	cuddDeref(t);
	cuddDeref(e);
    } else {
	if (Cudd_IsComplement(t)) {
	    r = cuddUniqueInter(manager,(int)index,Cudd_Not(t),Cudd_Not(e));
	    if (r == NULL) {
		Cudd_IterDerefBdd(manager, t);
		Cudd_IterDerefBdd(manager, e);
		return(NULL);
	    }
	    r = Cudd_Not(r);
	} else {
	    r = cuddUniqueInter(manager,(int)index,t,e);
	    if (r == NULL) {
		Cudd_IterDerefBdd(manager, t);
		Cudd_IterDerefBdd(manager, e);
		return(NULL);
	    }
	}
	cuddDeref(e);
	cuddDeref(t);
    }
    cuddCacheInsert(manager, DD_BDD_XOR_EXIST_ABSTRACT_TAG, f, g, cube, r);
    return (r);

} /* end of cuddBddXorExistAbstractRecur */


/**
  @brief Performs the recursive steps of Cudd_bddBoleanDiff.

  @details Exploits the fact that dF/dx = dF'/dx.

  @return the %BDD obtained by XORing the cofactors of f with respect
  to var if successful; NULL otherwise.

  @sideeffect None

*/
DdNode *
cuddBddBooleanDiffRecur(
  DdManager * manager,
  DdNode * f,
  DdNode * var)
{
    DdNode *T, *E, *res, *res1, *res2;

    statLine(manager);
    if (cuddI(manager,f->index) > manager->perm[var->index]) {
	/* f does not depend on var. */
	return(Cudd_Not(DD_ONE(manager)));
    }

    /* From now on, f is non-constant. */

    /* If the two indices are the same, so are their levels. */
    if (f->index == var->index) {
	res = cuddBddXorRecur(manager, cuddT(f), cuddE(f));
        return(res);
    }

    /* From now on, cuddI(manager,f->index) < cuddI(manager,cube->index). */

    /* Check the cache. */
    res = cuddCacheLookup2(manager, cuddBddBooleanDiffRecur, f, var);
    if (res != NULL) {
	return(res);
    }

    /* Compute the cofactors of f. */
    T = cuddT(f); E = cuddE(f);

    res1 = cuddBddBooleanDiffRecur(manager, T, var);
    if (res1 == NULL) return(NULL);
    cuddRef(res1);
    res2 = cuddBddBooleanDiffRecur(manager, Cudd_Regular(E), var);
    if (res2 == NULL) {
	Cudd_IterDerefBdd(manager, res1);
	return(NULL);
    }
    cuddRef(res2);
    /* ITE takes care of possible complementation of res1 and of the
    ** case in which res1 == res2. */
    res = cuddBddIteRecur(manager, manager->vars[f->index], res1, res2);
    if (res == NULL) {
	Cudd_IterDerefBdd(manager, res1);
	Cudd_IterDerefBdd(manager, res2);
	return(NULL);
    }
    cuddDeref(res1);
    cuddDeref(res2);
    cuddCacheInsert2(manager, cuddBddBooleanDiffRecur, f, var, res);
    return(res);

} /* end of cuddBddBooleanDiffRecur */


/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**
  @brief Checks whether cube is a %BDD representing the product of
  positive literals.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
static int
bddCheckPositiveCube(
  DdManager * manager,
  DdNode * cube)
{
    if (Cudd_IsComplement(cube)) return(0);
    if (cube == DD_ONE(manager)) return(1);
    if (cuddIsConstant(cube)) return(0);
    if (cuddE(cube) == Cudd_Not(DD_ONE(manager))) {
        return(bddCheckPositiveCube(manager, cuddT(cube)));
    }
    return(0);

} /* end of bddCheckPositiveCube */

DdNode *
Cudd_bddDeterminizeController(
	DdManager * manager,
	DdNode * f,
	DdNode * cube) // the variables to determinize
{
	DdNode *res, *cube_top, *vars_and, *cur_var, *util;
	int i, j, *cube_support, *old_order, *new_order;

	if (bddCheckPositiveCube(manager, cube) == 0) {
		(void)fprintf(manager->err, "Error:  Can only abstract cubes");
		return(NULL);
	}

	cube_support = Cudd_SupportIndex(manager, cube);

	old_order = (int*)malloc((manager->size) * sizeof(int)); //maps level to index
	if (old_order == NULL) {
		return NULL;
	}

	new_order = (int*)malloc((manager->size) * sizeof(int)); //maps level to index
	if (new_order == NULL) {
		return NULL;
	}


	for (i = 0; i < manager->size; i++) {
		old_order[i] = manager->invperm[i];

	}

	for (i = 0, j = 0; i < manager->size; i++) {
		if (cube_support[i] != 1) {
			new_order[j] = i;
			j++;
		}
	}
	for (i = 0; i < manager->size; i++) {
		if (cube_support[i] == 1) {
			new_order[j] = i;
			j++;
		}
	}

	do {
	//int auto_reorder = manager->autoDyn;
		Cudd_ShuffleHeap(manager, new_order); /*reorder variables, such that the vatiables we want to determinize will appear last*/
		manager->reordered = 0;
		//Cudd_AutodynDisable(manager);
		res = cuddBddDeterminizeControllerRecur(manager, f, cube);
	} while (manager->reordered == 1);

	Cudd_ReduceHeap(manager, CUDD_REORDER_SAME, 10);
	
	//if (auto_reorder) {
	//	Cudd_AutodynEnable(manager, CUDD_REORDER_SAME);
	//}

	free(old_order);
	free(new_order);
	return(res);


} /* end of Cudd_bddDeterminizeController */

DdNode *
cuddBddDeterminizeControllerRecur(
	DdManager * manager,
	DdNode * f,
	DdNode * det_cube)
{
	DdNode	*F, *T, *E, *res, *res1, *res2, *one, *zero, *cur_cube, *fn; //*var, *top_cube;
	unsigned char flagT, flagE;
	int *cube_arr, i;
	DdGen *first_cube;
	CUDD_VALUE_TYPE cube_val;
	statLine(manager);
	one = DD_ONE(manager);
	zero = Cudd_Not(DD_ONE(manager));

	/* Cube is guaranteed to be a cube at this point.
	*/

	if (det_cube == one) { /*there are no variables left*/
		return(f);
	}

	if (f == zero) { /*f is a zero constant -> no need to perform an AND operation, because it is ZERO anyways!*/
		return zero;
	}

	F = Cudd_Regular(f);
	

	/*cube != one -> we still have variables to check for*/
	/* a variable (var) that does not appear in f (but only in the cube), so make it appear in f in its positive form.
	we achieve this by performing: f AND var.
	If we reached a non-zero constant node of f, and we have a variable that does not appear in f, then do the same.
	*/

	if (F->ref != 1 && ((res = cuddCacheLookup2(manager, Cudd_bddDeterminizeController, f, det_cube)) != NULL)) {
		return(res);
	}

	checkWhetherToGiveUp(manager);

	if ((cuddI(manager, F->index) > cuddI(manager, det_cube->index)) || (f == one)) {
		res1 = cuddBddDeterminizeControllerRecur(manager, f, cuddT(det_cube));
		if (res1 == NULL){
			return(NULL);
		}
		Cudd_Ref(res1);
		//Cudd_Ref(zero);
		//Cudd_Ref(one);

	/*	top_cube = cuddUniqueInter(manager, det_cube->index, one, zero);
		if (top_cube == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			Cudd_Deref(zero);
			Cudd_Deref(one);
			return(NULL);
		}*/
		//Cudd_Ref(top_cube);
		res = cuddBddAndRecur(manager, res1, manager->vars[det_cube->index]);
		//res = cuddBddAndRecur(manager, res1, top_cube); /*perform AND operation with the top variable of the cube*/
		if (res == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			//Cudd_Deref(zero);
			//Cudd_Deref(one);
			return(NULL);
		}
		Cudd_Ref(res);
		//Cudd_RecursiveDeref(manager, top_cube);
		Cudd_RecursiveDeref(manager, res1);
		//Cudd_Deref(zero);
		//Cudd_Deref(one);
		return(res);
	}

	/* Use the "internal" procedure to be alerted in case of
	** dynamic reordering. If dynamic reordering occurs, we
	** have to abort the entire abstraction.
	*/

	T = cuddT(F);
	E = cuddE(F);

	if (f != F) { //if f is complemented, complement its children
		T = Cudd_Not(T);
		E = Cudd_Not(E);
	}

	/*	If the two indices are the same, so are their levels.
	a variable that appears both in f and the cube.
	*/
	if (F->index == det_cube->index) {
		if (T != zero) {
			first_cube = Cudd_FirstCube(manager, T, &cube_arr, &cube_val);
			flagT = 1;
			flagE = 0;
		}
		else { // (T == zero)
			first_cube = Cudd_FirstCube(manager, E, &cube_arr, &cube_val);
			flagT = 0;
			flagE = 1;
		}
		if (first_cube == NULL) {
			free(cube_arr);
			return NULL;
		}

		cur_cube = one;
		cuddRef(cur_cube);

		for (i = manager->size - 1; i >= 0; i--) {
			if (cuddI(manager, i) > cuddI(manager, F->index)) { // sys var that is ordered after the current sys variable 
				//cuddRef(one);
				cuddRef(zero);
				//var = cuddUniqueInter(manager, i, one, zero);
				//if (var == NULL) {
				//	Cudd_RecursiveDeref(manager, cur_cube);
				//	return NULL;
				//}
				//cuddRef(var);
				//cuddDeref(one);

				if (cube_arr[i] != 0) { //positive or dont care
					//fn = cuddBddIteRecur(manager, var, cur_cube, zero);
					fn = cuddBddIteRecur(manager, manager->vars[i], cur_cube, zero);
				}
				else { //negative
				//	fn = cuddBddIteRecur(manager, var, zero, cur_cube);
					fn = cuddBddIteRecur(manager, manager->vars[i], zero, cur_cube);
				}
				if (fn == NULL) {
					Cudd_RecursiveDeref(manager, cur_cube);
					//Cudd_RecursiveDeref(manager, var);
					cuddDeref(zero);
					Cudd_GenFree(first_cube);
					return(NULL);
				}
				cuddRef(fn);
				cuddDeref(zero);
				Cudd_RecursiveDeref(manager, cur_cube);
				//Cudd_RecursiveDeref(manager, var);
				cur_cube = fn;
			}
		}

		Cudd_GenFree(first_cube);
		//cuddRef(one);
		cuddRef(zero);
		//res1 = cuddUniqueInter(manager, (int)F->index, one, zero);
		//if (res1 == NULL) {
		//	Cudd_RecursiveDeref(manager, cur_cube);
		//	return NULL;
		//}
		//cuddRef(res1);
		//cuddDeref(one);

		if (flagT && !flagE) { //make the 'then' child to be cur_cube
			//res = cuddBddIteRecur(manager, res1, cur_cube, zero);
			res = cuddBddIteRecur(manager, manager->vars[F->index], cur_cube, zero);
			

		}
		else { //!flagT && flagE : make the 'else' child to be cur_cube
			//res = cuddBddIteRecur(manager, res1, zero, cur_cube);
			res = cuddBddIteRecur(manager, manager->vars[F->index], zero, cur_cube);
		}
		if (res == NULL) {
			cuddDeref(zero);
			Cudd_RecursiveDeref(manager, cur_cube);
			//Cudd_RecursiveDeref(manager, res1);
			return(NULL);
		}
		cuddRef(res);
		cuddDeref(zero);
		Cudd_RecursiveDeref(manager, cur_cube);
		//Cudd_RecursiveDeref(manager, res1);
		if (F->ref != 1) {
			cuddCacheInsert2(manager, Cudd_bddDeterminizeController, f, det_cube, res);
		}
		return (res);
	}
	else { /* if (cuddI(manager,F->index) < cuddI(manager,det_cube->index)) : a variable that does not appear in the cube (but only in f)*/
		res1 = cuddBddDeterminizeControllerRecur(manager, T, det_cube);
		if (res1 == NULL) return(NULL);
		cuddRef(res1);
		
		res2 = cuddBddDeterminizeControllerRecur(manager, E, det_cube);
		if (res2 == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			return(NULL);
		}
		cuddRef(res2);
		
		//Cudd_RecursiveDeref(manager, T);
		//Cudd_RecursiveDeref(manager, E);

		/*a variable that does not appear in the cube (therefore, can be non-deterministic): therefore, we perform a regular BDD/ADD reduce operation*/
		if (res1 == res2) {
			res = res1;
		}
		else {
			res = cuddBddIteRecur(manager, manager->vars[F->index], res1, res2);
			//cuddDeref(zero);
			//cuddDeref(one);
		}
		if (res == NULL) {
			//Cudd_RecursiveDeref(manager, res1);
			//Cudd_RecursiveDeref(manager, res2);
			cuddDeref(res1);
			cuddDeref(res2);
			return(NULL);
		}
		cuddRef(res);
		cuddDeref(res1);
		cuddDeref(res2);
		//Cudd_RecursiveDeref(manager, res1);
		//Cudd_RecursiveDeref(manager, res2);
		if (F->ref != 1) {
			cuddCacheInsert2(manager, Cudd_bddDeterminizeController, f, det_cube, res);
		}
		return(res);
	}
} /* end of cuddBddDeterminizeControllerRecur */
