/**
  @file 

  @ingroup cudd

  @brief Quantification functions for ADDs.

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

static int addCheckPositiveCube (DdManager *manager, DdNode *cube);

/** \endcond */


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**
  @brief Existentially Abstracts all the variables in cube from f.

  @details Abstracts all the variables in cube from f by summing
  over all possible values taken by the variables.

  @return the abstracted %ADD.

  @sideeffect None

  @see Cudd_addUnivAbstract Cudd_bddExistAbstract
  Cudd_addOrAbstract

*/
DdNode *
Cudd_addExistAbstract(
  DdManager * manager,
  DdNode * f,
  DdNode * cube)
{
    DdNode *res;

    if (addCheckPositiveCube(manager, cube) == 0) {
        (void) fprintf(manager->err,"Error: Can only abstract cubes");
        return(NULL);
    }

    do {
	manager->reordered = 0;
	res = cuddAddExistAbstractRecur(manager, f, cube);
    } while (manager->reordered == 1);
    if (manager->errorCode == CUDD_TIMEOUT_EXPIRED && manager->timeoutHandler) {
        manager->timeoutHandler(manager, manager->tohArg);
    }

    return(res);

} /* end of Cudd_addExistAbstract */

  /**Function********************************************************************

  Synopsis    [Abstracts all the variables in cube from f and applies minimum operation.]

  Description [Abstracts all the variables in cube from f by applying minimum operation
  over all possible values taken by the variables. Returns the
  abstracted ADD.]

  SideEffects [None]

  SeeAlso     [Cudd_addMaxAbstract Cudd_addUnivAbstract Cudd_bddExistAbstract
  Cudd_addOrAbstract]

  ******************************************************************************/
DdNode *
Cudd_addMinAbstract(
	DdManager * manager,
	DdNode * f,
	DdNode * cube)
{
	DdNode *res;

	if (addCheckPositiveCube(manager, cube) == 0) {
		(void)fprintf(manager->err, "Error:  Can only abstract cubes");
		return(NULL);
	}

	do {
		manager->reordered = 0;
		res = cuddAddMinAbstractRecur(manager, f, cube);
	} while (manager->reordered == 1);

	return(res);


} /* end of Cudd_addMinAbstract */
  /**Function********************************************************************

  Synopsis    [Abstracts all the variables in cube from f and applies maximum operation.]

  Description [Abstracts all the variables in cube from f by applying maximum operation
  over all possible values taken by the variables. Returns the
  abstracted ADD.]

  SideEffects [None]

  SeeAlso     [Cudd_addMinAbstract Cudd_addUnivAbstract Cudd_bddExistAbstract
  Cudd_addOrAbstract]

  ******************************************************************************/
DdNode *
Cudd_addMaxAbstract(
	DdManager * manager,
	DdNode * f,
	DdNode * cube)
{
	DdNode *res;

	if (addCheckPositiveCube(manager, cube) == 0) {
		(void)fprintf(manager->err, "Error:  Can only abstract cubes");
		return(NULL);
	}

	do {
		manager->reordered = 0;
		res = cuddAddMaxAbstractRecur(manager, f, cube);
	} while (manager->reordered == 1);

	return(res);


} /* end of Cudd_addMaxAbstract */

DdNode *
cuddAddMinAbstractRecur(
	DdManager * manager,
	DdNode * f,
	DdNode * cube)
{
	DdNode	*T, *E, *res, *res1, *res2, *one;

	statLine(manager);
	one = DD_ONE(manager);

	/* Cube is guaranteed to be a cube at this point.
	*/
	if (cube == one || cuddIsConstant(f)) {
		return(f);
	}

	/* Abstract a variable that does not appear in f. */
	if (cuddI(manager, f->index) > cuddI(manager, cube->index)) {
		res = cuddAddMinAbstractRecur(manager, f, cuddT(cube));
		if (res == NULL) return(NULL);
		/* Use the "internal" procedure to be alerted in case of
		** dynamic reordering. If dynamic reordering occurs, we
		** have to abort the entire abstraction.
		*/
		return(res);
	}

	if ((res = cuddCacheLookup2(manager, Cudd_addMinAbstract, f, cube)) != NULL) {
		return(res);
	}

	T = cuddT(f);
	E = cuddE(f);

	/* If the two indices are the same, so are their levels. */
	if (f->index == cube->index) {
		res1 = cuddAddMinAbstractRecur(manager, T, cuddT(cube));
		if (res1 == NULL) return(NULL);
		cuddRef(res1);
		res2 = cuddAddMinAbstractRecur(manager, E, cuddT(cube));
		if (res2 == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			return(NULL);
		}
		cuddRef(res2);
		res = cuddAddApplyRecur(manager, Cudd_addMinimum, res1, res2);
		if (res == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			Cudd_RecursiveDeref(manager, res2);
			return(NULL);
		}
		cuddRef(res);
		Cudd_RecursiveDeref(manager, res1);
		Cudd_RecursiveDeref(manager, res2);
		cuddCacheInsert2(manager, Cudd_addMinAbstract, f, cube, res);
		cuddDeref(res);
		return(res);
	}
	else { /* if (cuddI(manager,f->index) < cuddI(manager,cube->index)) */
		res1 = cuddAddMinAbstractRecur(manager, T, cube);
		if (res1 == NULL) return(NULL);
		cuddRef(res1);
		res2 = cuddAddMinAbstractRecur(manager, E, cube);
		if (res2 == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			return(NULL);
		}
		cuddRef(res2);
		res = (res1 == res2) ? res1 :
			cuddUniqueInter(manager, (int)f->index, res1, res2);
		if (res == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			Cudd_RecursiveDeref(manager, res2);
			return(NULL);
		}
		cuddDeref(res1);
		cuddDeref(res2);
		cuddCacheInsert2(manager, Cudd_addMinAbstract, f, cube, res);
		return(res);
	}

} /* end of cuddAddMinAbstractRecur */

/**
  @brief Universally Abstracts all the variables in cube from f.

  @details Abstracts all the variables in cube from f by taking
  the product over all possible values taken by the variable.

  @return the abstracted %ADD if successful; NULL otherwise.

  @sideeffect None

  @see Cudd_addExistAbstract Cudd_bddUnivAbstract
  Cudd_addOrAbstract

*/
DdNode *
Cudd_addUnivAbstract(
  DdManager * manager,
  DdNode * f,
  DdNode * cube)
{
    DdNode		*res;

    if (addCheckPositiveCube(manager, cube) == 0) {
	(void) fprintf(manager->err,"Error:  Can only abstract cubes");
	return(NULL);
    }

    do {
	manager->reordered = 0;
	res = cuddAddUnivAbstractRecur(manager, f, cube);
    } while (manager->reordered == 1);
    if (manager->errorCode == CUDD_TIMEOUT_EXPIRED && manager->timeoutHandler) {
        manager->timeoutHandler(manager, manager->tohArg);
    }

    return(res);

} /* end of Cudd_addUnivAbstract */

DdNode *
Cudd_addDeterminizeController(
	DdManager * manager,
	DdNode * f,
	DdNode * cube) // the variables to determinize
{
	DdNode *res, *cube_top, *vars_and, *cur_var, *util;
	int i, j, *cube_support, *old_order, *new_order;

	if (addCheckPositiveCube(manager, cube) == 0) {
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
		Cudd_ShuffleHeap(manager, new_order); /*reorder variables, such that the vatiables we want to determinize will appear last*/
		manager->reordered = 0;
		res = cuddAddDeterminizeControllerRecur2(manager, f, cube);
	} while (manager->reordered == 1);

	Cudd_ReduceHeap(manager, CUDD_REORDER_SAME, 10);

	free(old_order);
	free(new_order);
	return(res);


} /* end of Cudd_addDeterminizeController */


DdNode *
cuddAddMaxAbstractRecur(
	DdManager * manager,
	DdNode * f,
	DdNode * cube)
{
	DdNode	*T, *E, *res, *res1, *res2, *one;

	statLine(manager);
	one = DD_ONE(manager);

	/* Cube is guaranteed to be a cube at this point.
	*/
	if (cube == one || cuddIsConstant(f)) {
		return(f);
	}

	/* Abstract a variable that does not appear in f. */
	if (cuddI(manager, f->index) > cuddI(manager, cube->index)) {
		res = cuddAddMaxAbstractRecur(manager, f, cuddT(cube));
		if (res == NULL) return(NULL);
		/* Use the "internal" procedure to be alerted in case of
		** dynamic reordering. If dynamic reordering occurs, we
		** have to abort the entire abstraction.
		*/
		return(res);
	}

	if ((res = cuddCacheLookup2(manager, Cudd_addMaxAbstract, f, cube)) != NULL) {
		return(res);
	}

	T = cuddT(f);
	E = cuddE(f);

	/* If the two indices are the same, so are their levels. */
	if (f->index == cube->index) {
		res1 = cuddAddMaxAbstractRecur(manager, T, cuddT(cube));
		if (res1 == NULL) return(NULL);
		cuddRef(res1);
		res2 = cuddAddMaxAbstractRecur(manager, E, cuddT(cube));
		if (res2 == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			return(NULL);
		}
		cuddRef(res2);
		res = cuddAddApplyRecur(manager, Cudd_addMaximum, res1, res2);
		if (res == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			Cudd_RecursiveDeref(manager, res2);
			return(NULL);
		}
		cuddRef(res);
		Cudd_RecursiveDeref(manager, res1);
		Cudd_RecursiveDeref(manager, res2);
		cuddCacheInsert2(manager, Cudd_addMaxAbstract, f, cube, res);
		cuddDeref(res);
		return(res);
	}
	else { /* if (cuddI(manager,f->index) < cuddI(manager,cube->index)) */
		res1 = cuddAddMaxAbstractRecur(manager, T, cube);
		if (res1 == NULL) return(NULL);
		cuddRef(res1);
		res2 = cuddAddMaxAbstractRecur(manager, E, cube);
		if (res2 == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			return(NULL);
		}
		cuddRef(res2);
		res = (res1 == res2) ? res1 :
			cuddUniqueInter(manager, (int)f->index, res1, res2);
		if (res == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			Cudd_RecursiveDeref(manager, res2);
			return(NULL);
		}
		cuddDeref(res1);
		cuddDeref(res2);
		cuddCacheInsert2(manager, Cudd_addMaxAbstract, f, cube, res);
		return(res);
	}

} /* end of cuddAddMaxAbstractRecur */

/**
  @brief Disjunctively abstracts all the variables in cube from the
  0-1 %ADD f.

  @details Abstracts all the variables in cube from the 0-1 %ADD f
  by taking the disjunction over all possible values taken by the
  variables.

  @return the abstracted %ADD if successful; NULL otherwise.

  @sideeffect None

  @see Cudd_addUnivAbstract Cudd_addExistAbstract

*/
DdNode *
Cudd_addOrAbstract(
  DdManager * manager,
  DdNode * f,
  DdNode * cube)
{
    DdNode *res;

    if (addCheckPositiveCube(manager, cube) == 0) {
        (void) fprintf(manager->err,"Error: Can only abstract cubes");
        return(NULL);
    }

    do {
	manager->reordered = 0;
	res = cuddAddOrAbstractRecur(manager, f, cube);
    } while (manager->reordered == 1);
    if (manager->errorCode == CUDD_TIMEOUT_EXPIRED && manager->timeoutHandler) {
        manager->timeoutHandler(manager, manager->tohArg);
    }
    return(res);

} /* end of Cudd_addOrAbstract */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/


/**
  @brief Performs the recursive step of Cudd_addExistAbstract.

  @details Returns the %ADD obtained by abstracting the variables of
  cube from f, if successful; NULL otherwise.

  @sideeffect None

*/
DdNode *
cuddAddExistAbstractRecur(
  DdManager * manager,
  DdNode * f,
  DdNode * cube)
{
    DdNode	*T, *E, *res, *res1, *res2, *zero;

    statLine(manager);
    zero = DD_ZERO(manager);

    /* Cube is guaranteed to be a cube at this point. */	
    if (f == zero || cuddIsConstant(cube)) {  
        return(f);
    }

    /* Abstract a variable that does not appear in f => multiply by 2. */
    if (cuddI(manager,f->index) > cuddI(manager,cube->index)) {
	res1 = cuddAddExistAbstractRecur(manager, f, cuddT(cube));
	if (res1 == NULL) return(NULL);
	cuddRef(res1);
	/* Use the "internal" procedure to be alerted in case of
	** dynamic reordering. If dynamic reordering occurs, we
	** have to abort the entire abstraction.
	*/
	res = cuddAddApplyRecur(manager,Cudd_addPlus,res1,res1);
	if (res == NULL) {
	    Cudd_RecursiveDeref(manager,res1);
	    return(NULL);
	}
	cuddRef(res);
	Cudd_RecursiveDeref(manager,res1);
	cuddDeref(res);
        return(res);
    }

    if ((res = cuddCacheLookup2(manager, Cudd_addExistAbstract, f, cube)) != NULL) {
	return(res);
    }

    checkWhetherToGiveUp(manager);

    T = cuddT(f);
    E = cuddE(f);

    /* If the two indices are the same, so are their levels. */
    if (f->index == cube->index) {
	res1 = cuddAddExistAbstractRecur(manager, T, cuddT(cube));
	if (res1 == NULL) return(NULL);
        cuddRef(res1);
	res2 = cuddAddExistAbstractRecur(manager, E, cuddT(cube));
	if (res2 == NULL) {
	    Cudd_RecursiveDeref(manager,res1);
	    return(NULL);
	}
        cuddRef(res2);
	res = cuddAddApplyRecur(manager, Cudd_addPlus, res1, res2);
	if (res == NULL) {
	    Cudd_RecursiveDeref(manager,res1);
	    Cudd_RecursiveDeref(manager,res2);
	    return(NULL);
	}
	cuddRef(res);
	Cudd_RecursiveDeref(manager,res1);
	Cudd_RecursiveDeref(manager,res2);
	cuddCacheInsert2(manager, Cudd_addExistAbstract, f, cube, res);
	cuddDeref(res);
        return(res);
    } else { /* if (cuddI(manager,f->index) < cuddI(manager,cube->index)) */
	res1 = cuddAddExistAbstractRecur(manager, T, cube);
	if (res1 == NULL) return(NULL);
        cuddRef(res1);
	res2 = cuddAddExistAbstractRecur(manager, E, cube);
	if (res2 == NULL) {
	    Cudd_RecursiveDeref(manager,res1);
	    return(NULL);
	}
        cuddRef(res2);
	res = (res1 == res2) ? res1 :
	    cuddUniqueInter(manager, (int) f->index, res1, res2);
	if (res == NULL) {
	    Cudd_RecursiveDeref(manager,res1);
	    Cudd_RecursiveDeref(manager,res2);
	    return(NULL);
	}
	cuddDeref(res1);
	cuddDeref(res2);
	cuddCacheInsert2(manager, Cudd_addExistAbstract, f, cube, res);
        return(res);
    }	    

} /* end of cuddAddExistAbstractRecur */


/**
  @brief Performs the recursive step of Cudd_addUnivAbstract.

  @return the %ADD obtained by abstracting the variables of cube from
  f, if successful; NULL otherwise.

  @sideeffect None

*/
DdNode *
cuddAddUnivAbstractRecur(
  DdManager * manager,
  DdNode * f,
  DdNode * cube)
{
    DdNode	*T, *E, *res, *res1, *res2, *one, *zero;

    statLine(manager);
    one = DD_ONE(manager);
    zero = DD_ZERO(manager);

    /* Cube is guaranteed to be a cube at this point.
    ** zero and one are the only constatnts c such that c*c=c.
    */
    if (f == zero || f == one || cube == one) {  
	return(f);
    }

    /* Abstract a variable that does not appear in f. */
    if (cuddI(manager,f->index) > cuddI(manager,cube->index)) {
	res1 = cuddAddUnivAbstractRecur(manager, f, cuddT(cube));
	if (res1 == NULL) return(NULL);
	cuddRef(res1);
	/* Use the "internal" procedure to be alerted in case of
	** dynamic reordering. If dynamic reordering occurs, we
	** have to abort the entire abstraction.
	*/
	res = cuddAddApplyRecur(manager, Cudd_addTimes, res1, res1);
	if (res == NULL) {
	    Cudd_RecursiveDeref(manager,res1);
	    return(NULL);
	}
	cuddRef(res);
	Cudd_RecursiveDeref(manager,res1);
	cuddDeref(res);
	return(res);
    }

    if ((res = cuddCacheLookup2(manager, Cudd_addUnivAbstract, f, cube)) != NULL) {
	return(res);
    }

    checkWhetherToGiveUp(manager);

    T = cuddT(f);
    E = cuddE(f);

    /* If the two indices are the same, so are their levels. */
    if (f->index == cube->index) {
	res1 = cuddAddUnivAbstractRecur(manager, T, cuddT(cube));
	if (res1 == NULL) return(NULL);
        cuddRef(res1);
	res2 = cuddAddUnivAbstractRecur(manager, E, cuddT(cube));
	if (res2 == NULL) {
	    Cudd_RecursiveDeref(manager,res1);
	    return(NULL);
	}
        cuddRef(res2);
	res = cuddAddApplyRecur(manager, Cudd_addTimes, res1, res2);
	if (res == NULL) {
	    Cudd_RecursiveDeref(manager,res1);
	    Cudd_RecursiveDeref(manager,res2);
	    return(NULL);
	}
	cuddRef(res);
	Cudd_RecursiveDeref(manager,res1);
	Cudd_RecursiveDeref(manager,res2);
	cuddCacheInsert2(manager, Cudd_addUnivAbstract, f, cube, res);
	cuddDeref(res);
        return(res);
    } else { /* if (cuddI(manager,f->index) < cuddI(manager,cube->index)) */
	res1 = cuddAddUnivAbstractRecur(manager, T, cube);
	if (res1 == NULL) return(NULL);
        cuddRef(res1);
	res2 = cuddAddUnivAbstractRecur(manager, E, cube);
	if (res2 == NULL) {
	    Cudd_RecursiveDeref(manager,res1);
	    return(NULL);
	}
        cuddRef(res2);
	res = (res1 == res2) ? res1 :
	    cuddUniqueInter(manager, (int) f->index, res1, res2);
	if (res == NULL) {
	    Cudd_RecursiveDeref(manager,res1);
	    Cudd_RecursiveDeref(manager,res2);
	    return(NULL);
	}
	cuddDeref(res1);
	cuddDeref(res2);
	cuddCacheInsert2(manager, Cudd_addUnivAbstract, f, cube, res);
        return(res);
    }

} /* end of cuddAddUnivAbstractRecur */


/**
  @brief Performs the recursive step of Cudd_addOrAbstract.

  @return the %ADD obtained by abstracting the variables of cube from
  f, if successful; NULL otherwise.

  @sideeffect None

*/
DdNode *
cuddAddOrAbstractRecur(
  DdManager * manager,
  DdNode * f,
  DdNode * cube)
{
    DdNode	*T, *E, *res, *res1, *res2, *one;

    statLine(manager);
    one = DD_ONE(manager);

    /* Cube is guaranteed to be a cube at this point. */
    if (cuddIsConstant(f) || cube == one) {  
	return(f);
    }

    /* Abstract a variable that does not appear in f. */
    if (cuddI(manager,f->index) > cuddI(manager,cube->index)) {
	res = cuddAddOrAbstractRecur(manager, f, cuddT(cube));
	return(res);
    }

    if ((res = cuddCacheLookup2(manager, Cudd_addOrAbstract, f, cube)) != NULL) {
	return(res);
    }

    checkWhetherToGiveUp(manager);

    T = cuddT(f);
    E = cuddE(f);

    /* If the two indices are the same, so are their levels. */
    if (f->index == cube->index) {
	res1 = cuddAddOrAbstractRecur(manager, T, cuddT(cube));
	if (res1 == NULL) return(NULL);
        cuddRef(res1);
	if (res1 != one) {
	    res2 = cuddAddOrAbstractRecur(manager, E, cuddT(cube));
	    if (res2 == NULL) {
		Cudd_RecursiveDeref(manager,res1);
		return(NULL);
	    }
	    cuddRef(res2);
	    res = cuddAddApplyRecur(manager, Cudd_addOr, res1, res2);
	    if (res == NULL) {
		Cudd_RecursiveDeref(manager,res1);
		Cudd_RecursiveDeref(manager,res2);
		return(NULL);
	    }
	    cuddRef(res);
	    Cudd_RecursiveDeref(manager,res1);
	    Cudd_RecursiveDeref(manager,res2);
	} else {
	    res = res1;
	}
	cuddCacheInsert2(manager, Cudd_addOrAbstract, f, cube, res);
	cuddDeref(res);
        return(res);
    } else { /* if (cuddI(manager,f->index) < cuddI(manager,cube->index)) */
	res1 = cuddAddOrAbstractRecur(manager, T, cube);
	if (res1 == NULL) return(NULL);
        cuddRef(res1);
	res2 = cuddAddOrAbstractRecur(manager, E, cube);
	if (res2 == NULL) {
	    Cudd_RecursiveDeref(manager,res1);
	    return(NULL);
	}
        cuddRef(res2);
	res = (res1 == res2) ? res1 :
	    cuddUniqueInter(manager, (int) f->index, res1, res2);
	if (res == NULL) {
	    Cudd_RecursiveDeref(manager,res1);
	    Cudd_RecursiveDeref(manager,res2);
	    return(NULL);
	}
	cuddDeref(res1);
	cuddDeref(res2);
	cuddCacheInsert2(manager, Cudd_addOrAbstract, f, cube, res);
        return(res);
    }

} /* end of cuddAddOrAbstractRecur */



/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/


/**
  @brief Checks whether cube is an %ADD representing the product
  of positive literals.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
static int
addCheckPositiveCube(
  DdManager * manager,
  DdNode * cube)
{
    if (Cudd_IsComplement(cube)) return(0);
    if (cube == DD_ONE(manager)) return(1);
    if (cuddIsConstant(cube)) return(0);
    if (cuddE(cube) == DD_ZERO(manager)) {
        return(addCheckPositiveCube(manager, cuddT(cube)));
    }
    return(0);

} /* end of addCheckPositiveCube */


DdNode *
cuddAddDeterminizeControllerRecur2(
	DdManager * manager,
	DdNode * f,
	DdNode * det_cube)
{
	DdNode	*T, *E, *res, *res1, *res2, *one, *zero, *top_cube, *cur_cube, *var, *fn;
	unsigned char flagT, flagE;
	int *cube_arr, i;
	DdGen *first_cube;
	CUDD_VALUE_TYPE cube_val;
	statLine(manager);
	one = DD_ONE(manager);
	zero = DD_ZERO(manager);

	/* Cube is guaranteed to be a cube at this point.
	*/

	if (det_cube == one) { /*there are no variables left*/
		return(f);
	}

	if (f == zero) { /*f is a zero constant -> no need to perform an AND operation, because it is ZERO anyways!*/
		return zero;
	}


	/*cube != one -> we still have variables to check for*/
	/*	a variable (var) that does not appear in f (but only in the cube), so make it appear in f in its positive form.
	we achieve this by performing: f AND var.
	If we reached a non-zero constant node of f, and we have a variable that does not appear in f, then do the same.
	*/
	if (cuddI(manager, f->index) > cuddI(manager, det_cube->index) || (cuddIsConstant(f))) {
		res1 = cuddAddDeterminizeControllerRecur2(manager, f, cuddT(det_cube));
		if (res1 == NULL) { return(NULL); }

		Cudd_Ref(res1);
		Cudd_Ref(zero);
		Cudd_Ref(one);

		top_cube = cuddUniqueInter(manager, det_cube->index, one, zero);
		//res = cuddUniqueInter(manager, det_cube->index, res1, zero);
		if (top_cube == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			Cudd_Deref(zero);
			Cudd_Deref(one);
			//Cudd_RecursiveDeref(manager, zero);
			return(NULL);
		}
		Cudd_Ref(top_cube);
		res = cuddAddApplyRecur(manager, Cudd_addTimes, res1, top_cube); /*perform AND operation with the top variable of the cube*/
		if (res == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			Cudd_RecursiveDeref(manager, zero);
			return(NULL);
		}
		Cudd_Ref(res);
		Cudd_RecursiveDeref(manager, top_cube);
		Cudd_RecursiveDeref(manager, res1);

		Cudd_Deref(zero);
		Cudd_Deref(one);

		//cuddDeref(res);
		return(res);
	}

	/* Use the "internal" procedure to be alerted in case of
	** dynamic reordering. If dynamic reordering occurs, we
	** have to abort the entire abstraction.
	*/

	if ((res = cuddCacheLookup2(manager, Cudd_addDeterminizeController, f, det_cube)) != NULL) {
		return(res);
	}

	T = cuddT(f);
	E = cuddE(f);

	/*	If the two indices are the same, so are their levels.
	a variable that appears both in f and the cube.
	*/
	if (f->index == det_cube->index) {
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
			if (cuddI(manager, i) > cuddI(manager, f->index)) { // sys var that is ordered after the current sys variable 
				cuddRef(one);
				cuddRef(zero);
				var = cuddUniqueInter(manager, i, one, zero);
				if (var == NULL) {
					Cudd_RecursiveDeref(manager, cur_cube);
					return NULL;
				}
				cuddRef(var);
				cuddDeref(one);

				if (cube_arr[i] != 0) { //positive or dont care
					fn = cuddAddIteRecur(manager, var, cur_cube, zero);
				}
				else { //negative
					fn = cuddAddIteRecur(manager, var, zero, cur_cube);
				}
				if (fn == NULL) {
					Cudd_RecursiveDeref(manager, cur_cube);
					Cudd_RecursiveDeref(manager, var);
					cuddDeref(zero);
					Cudd_GenFree(first_cube);
					return(NULL);
				}
				cuddRef(fn);
				cuddDeref(zero);
				Cudd_RecursiveDeref(manager, cur_cube);
				Cudd_RecursiveDeref(manager, var);
				cur_cube = fn;
			}
		}

		Cudd_GenFree(first_cube);
		cuddRef(one);
		cuddRef(zero);
		res1 = cuddUniqueInter(manager, (int)f->index, one, zero);
		if (res1 == NULL) {
			Cudd_RecursiveDeref(manager, cur_cube);
			return NULL;
		}
		cuddRef(res1);
		cuddDeref(one);

		if (flagT && !flagE) { //make the 'then' child to be cur_cube
			res = cuddAddIteRecur(manager, res1, cur_cube, zero);
		}
		else { //!flagT && flagE : make the 'else' child to be cur_cube
			res = cuddAddIteRecur(manager, res1, zero, cur_cube);
		}
		if (res == NULL) {
			Cudd_RecursiveDeref(manager, cur_cube);
			return(NULL);
		}
		cuddRef(res);
		cuddDeref(zero);
		Cudd_RecursiveDeref(manager, cur_cube);
		Cudd_RecursiveDeref(manager, res1);
		//cuddDeref(res);
		return (res);
	}
	else { /* if (cuddI(manager,f->index) < cuddI(manager,det_cube->index)) : a variable that does not appear in the cube (but only in f)*/
		res1 = cuddAddDeterminizeControllerRecur2(manager, T, det_cube);
		if (res1 == NULL) return(NULL);
		cuddRef(res1);
		res2 = cuddAddDeterminizeControllerRecur2(manager, E, det_cube);
		if (res2 == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			return(NULL);
		}
		cuddRef(res2);
		/*a variable that does not appear in the cube (therefore, can be non-deterministic): therefore, we perform a regular BDD/ADD reduce operation*/
		res = (res1 == res2) ? res1 :
			cuddUniqueInter(manager, (int)f->index, res1, res2);
		if (res == NULL) {
			Cudd_RecursiveDeref(manager, res1);
			Cudd_RecursiveDeref(manager, res2);
			return(NULL);
		}
		cuddRef(res);
		Cudd_RecursiveDeref(manager, res1);
		Cudd_RecursiveDeref(manager, res2);
		cuddCacheInsert2(manager, Cudd_addDeterminizeController, f, det_cube, res);
		//cuddDeref(res);
		return(res);
	}

} /* end of cuddAddDeterminizeControllerRecur2 */