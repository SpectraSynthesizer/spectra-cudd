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

#include <jni.h>
#include <jni_md.h>
#include <stdlib.h>
#include <assert.h>
#include <limits.h>
#include "cudd.h"
#include "cuddInt.h"
#include "mtr.h"
#include "cudd_jni.h"
#include <memory.h>
#include <stdio.h>
#include "synt.h"

#ifdef __linux__ 
#include<pthread.h>
#else 
#include <Synchapi.h>
#include <Windows.h>
#include <io.h>
#endif
/*
** WORKS WITH CUDD VERSION: 3.0.0 !!
** When casting from `int' to a pointer type, you should
** first cast to `intptr_cast_type'.  This is a type
** that is (a) the same size as a pointer, on most platforms,
** to avoid compiler warnings about casts from pointer to int of
** different size; and (b) guaranteed to be at least as big as
** `int'.
*/
#if __STDC_VERSION__ >= 199901
#include <inttypes.h>
#if INTPTR_MAX >= INT_MAX
typedef intptr_t intptr_cast_type;
#else /* no intptr_t, or intptr_t smaller than `int' */
typedef intmax_t intptr_cast_type;
#endif
#else
#include <stddef.h>
#include <limits.h>
#if PTRDIFF_MAX >= INT_MAX
typedef ptrdiff_t intptr_cast_type;
#else
typedef long long intptr_cast_type; // WAS CHANGED FROM int to long long
#endif
#endif

DdManager *manager;
static jlong bdd_one, bdd_zero, add_zero;

#ifdef __linux__ 
static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
#define LOCK pthread_mutex_lock(&mutex);
#define UNLOCK pthread_mutex_unlock(&mutex);
#else
static CRITICAL_SECTION critSec;
#define LOCK EnterCriticalSection(&critSec);
#define UNLOCK LeaveCriticalSection(&critSec);
#endif

static void die(JNIEnv *env, char* msg)
{
	jclass cls;
	cls = (*env)->FindClass(env, "java/lang/InternalError");
	if (cls != NULL) {
		(*env)->ThrowNew(env, cls, msg);
	}
	(*env)->DeleteLocalRef(env, cls);
}


/***************************************************************************
* Auxiliary Methods
*/
/*
A linked list that consists of all BDD and ADD constant nodes that are used
*/
typedef struct const_node {
	DdNode *terminal_node;
	struct const_node *next;
} const_node;

const_node *const_list, *head;

const char* BDDFACTORY_CLASS_NAME = "net/sf/javabdd/BDDFactory";

jfieldID JAVA_REORDER_NONE;
jfieldID JAVA_REORDER_RANDOM;
jfieldID JAVA_REORDER_SIFT;
jfieldID JAVA_REORDER_SIFTITE;
jfieldID JAVA_REORDER_WIN2;
jfieldID JAVA_REORDER_WIN2ITE;
jfieldID JAVA_REORDER_WIN3;
jfieldID JAVA_REORDER_WIN3ITE;

/*
BDD and ADD constant nodes linked list handling methods
*/
static void insert_new_const(JNIEnv *env, jclass cls, DdNode *const_ptr, unsigned char do_ref) {
	const_node *new_const = (const_node*)malloc(sizeof(const_node));
	if (new_const == NULL) {
		jclass cls = (*env)->FindClass(env, "java/lang/NullPointerException");
		(*env)->ThrowNew(env, cls, "CUDD library error: malloc() has failed in insert_new_const() method");
		(*env)->DeleteLocalRef(env, cls);
		return;
	}
	new_const->next = NULL;
	new_const->terminal_node = const_ptr;
	if (do_ref) {
		Cudd_Ref(new_const->terminal_node); //increase the reference count of the constant node
	}
	head->next = new_const;
	head = new_const;
}

static void init_const_list(JNIEnv *env, jclass cls, DdNode *const_ptr, unsigned char do_ref) {
	const_node *first_const = (const_node*)malloc(sizeof(const_node));
	if (first_const == NULL) {
		jclass cls = (*env)->FindClass(env, "java/lang/NullPointerException");
		(*env)->ThrowNew(env, cls, "CUDD library error: malloc() has failed in init_const_list() method");
		(*env)->DeleteLocalRef(env, cls);
		return;
	}
	const_list = first_const;
	head = first_const;
	head->next = NULL;
	head->terminal_node = const_ptr;
	if (do_ref) {
		Cudd_Ref(Cudd_Regular(head->terminal_node)); //increase the reference count of the constant node
	}
}

static void free_const_list(void) {
	const_node *p, *next;
	for (p = const_list; p != NULL; p = next) {
		Cudd_RecursiveDeref(manager, p->terminal_node); //decrease the reference count of the constant node
		next = p->next;
		free(p);
	}
	const_list = NULL;
	head = NULL;
}

static jboolean isJavaReorderMethod(JNIEnv *env, jclass cls,
	jfieldID id, jobject method)
{
	jobject field = (*env)->GetStaticObjectField(env, cls, id);
	return (*env)->IsSameObject(env, field, method);
}


static Cudd_ReorderingType getCUDDReorderMethod(JNIEnv *env,
	jobject javamethod)
{
	jclass cls = (*env)->FindClass(env, BDDFACTORY_CLASS_NAME);
	if (isJavaReorderMethod(env, cls, JAVA_REORDER_NONE, javamethod)) {
		return CUDD_REORDER_NONE;
	}
	else if (isJavaReorderMethod(env, cls, JAVA_REORDER_RANDOM, javamethod)) {
		return CUDD_REORDER_RANDOM;
	}
	else if (isJavaReorderMethod(env, cls, JAVA_REORDER_SIFT, javamethod)) {
		return CUDD_REORDER_SIFT;
	}
	else if (isJavaReorderMethod(env, cls, JAVA_REORDER_SIFTITE, javamethod)) {
		return CUDD_REORDER_SIFT_CONVERGE;
	}
	else if (isJavaReorderMethod(env, cls, JAVA_REORDER_WIN2, javamethod)) {
		return CUDD_REORDER_WINDOW2;
	}
	else if (isJavaReorderMethod(env, cls, JAVA_REORDER_WIN2ITE, javamethod)) {
		return CUDD_REORDER_WINDOW2_CONV;
	}
	else if (isJavaReorderMethod(env, cls, JAVA_REORDER_WIN3, javamethod)) {
		return CUDD_REORDER_WINDOW3;
	}
	else if (isJavaReorderMethod(env, cls, JAVA_REORDER_WIN3ITE, javamethod)) {
		return CUDD_REORDER_WINDOW3_CONV;
	}
	else {
		die(env, "Unknown Java reorder method!");
		return 0;
	}
}

static jfieldID getJavaReorderMethodId(JNIEnv *env,
	Cudd_ReorderingType cuddmethod)
{
	switch (cuddmethod) {
	case CUDD_REORDER_NONE:
		return JAVA_REORDER_NONE;
	case CUDD_REORDER_RANDOM:
		return JAVA_REORDER_RANDOM;
	case CUDD_REORDER_SIFT:
		return JAVA_REORDER_SIFT;
	case CUDD_REORDER_SIFT_CONVERGE:
		return JAVA_REORDER_SIFTITE;
	case CUDD_REORDER_WINDOW2:
		return JAVA_REORDER_WIN2;
	case CUDD_REORDER_WINDOW2_CONV:
		return JAVA_REORDER_WIN2ITE;
	case CUDD_REORDER_WINDOW3:
		return JAVA_REORDER_WIN3;
	case CUDD_REORDER_WINDOW3_CONV:
		return JAVA_REORDER_WIN3ITE;
	default:
		die(env, "Unknown reorder method in CUDD!");
		return 0;
	}
}
/*
Synopsis    [0-1 ADD condition check] -> Deprecated!

Description [0-1 ADD check operator for Apply.
Returns NULL if not a terminal case; 1 if (f=1 or f=0); 0 otherwise.
The g argument is ignored.]

SideEffects [None]

*/

/*
static DdNode *
Cudd_zeroOneAdd(
DdManager * dd,
DdNode * f)
{*/
/*
if (f == DD_ZERO(dd) || f == DD_ONE(dd)) {
return(DD_ONE(dd));
}

if (cuddIsConstant(f)) { */ /*terminal case, which is not 0-1*/
/*	return(DD_ZERO(dd));
}

return(NULL);*/ /*not a terminal case*/
/*}*/  /* end of zeroOneAdd */

static DdNode *applyOp
(JNIEnv *env, jlong a, jlong b, jint oper, jboolean is_add)
{
	DdNode* d;
	DdNode* e;
	DdNode* f;
	DdNode* tmp;
	d = (DdNode*)(intptr_cast_type)a;
	e = (DdNode*)(intptr_cast_type)b;

	if (!is_add) {
		switch (oper) {
		case 0: /* and */
			f = Cudd_bddAnd(manager, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 1: /* xor */
			f = Cudd_bddXor(manager, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 2: /* or */
			f = Cudd_bddOr(manager, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 3: /* nand */
			f = Cudd_bddNand(manager, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 4: /* nor */
			f = Cudd_bddNor(manager, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 5: /* imp */
			d = Cudd_Not(d);
			Cudd_Ref(d);
			f = Cudd_bddOr(manager, d, e);
			Cudd_Ref(Cudd_Regular(f));
			Cudd_RecursiveDeref(manager, d);
			break;
		case 6: /* biimp */
			f = Cudd_bddXnor(manager, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 7: /* diff */
			e = Cudd_Not(e);
			Cudd_Ref(e);
			f = Cudd_bddAnd(manager, d, e);
			Cudd_Ref(Cudd_Regular(f));
			Cudd_RecursiveDeref(manager, e);
			break;
		case 8: /* less */
			d = Cudd_Not(d);
			Cudd_Ref(d);
			f = Cudd_bddAnd(manager, d, e);
			Cudd_Ref(Cudd_Regular(f));
			Cudd_RecursiveDeref(manager, d);
			break;
		case 9: /* invimp */
			e = Cudd_Not(e);
			Cudd_Ref(e);
			f = Cudd_bddOr(manager, d, e);
			Cudd_Ref(Cudd_Regular(f));
			Cudd_RecursiveDeref(manager, e);
			break;
		default:
			die(env, "operation not supported");
			return INVALID_BDD;
		}
	}
	else { //is_add
		switch (oper) {
		case 0: /* and: 0-1 ADDs only */
			f = Cudd_addApply(manager, Cudd_addTimes, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 1: /* xor: 0-1 ADDs only */
			f = Cudd_addApply(manager, Cudd_addXor, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 2: /* or: 0-1 ADDs only*/
			f = Cudd_addApply(manager, Cudd_addOr, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 3: /* nand: 0-1 ADDs only */
			f = Cudd_addApply(manager, Cudd_addNand, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 4: /* nor: 0-1 ADDs only */
			f = Cudd_addApply(manager, Cudd_addNor, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 5: /* imp: 0-1 ADDs only */
			tmp = Cudd_addCmpl(manager, d); //negation (complement ADD)
			Cudd_Ref(tmp);
			f = Cudd_addApply(manager, Cudd_addOr, tmp, e);
			Cudd_Ref(Cudd_Regular(f));
			Cudd_RecursiveDeref(manager, tmp);
			break;
		case 6: /* biimp: 0-1 ADDs only */
			f = Cudd_addApply(manager, Cudd_addXnor, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 7: /* diff: 0-1 ADDs only  */
			e = Cudd_addCmpl(manager, e); //negation (complement ADD)
			Cudd_Ref(e);
			f = Cudd_addApply(manager, Cudd_addTimes, d, e);
			Cudd_Ref(Cudd_Regular(f));
			Cudd_RecursiveDeref(manager, e);
			break;
		case 8: /* less than (d < e)*/
			f = Cudd_addApply(manager, Cudd_addOneZeroMaximum, e, d);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 9: /* invimp: 0-1 ADDs only */
			e = Cudd_addCmpl(manager, e); //negation (complement ADD)
			Cudd_Ref(e);
			f = Cudd_addApply(manager, Cudd_addOr, d, e);
			Cudd_Ref(Cudd_Regular(f));
			Cudd_RecursiveDeref(manager, e);
			break;
		case 10: /* Arithmetic multiplication*/
			f = Cudd_addApply(manager, Cudd_addTimes, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 11: /* Arithmetic division*/
			f = Cudd_addApply(manager, Cudd_addDivide, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 12: /* Arithmetic addition*/
			f = Cudd_addApply(manager, Cudd_addPlus, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 13: /* Arithmetic subtraction*/
			f = Cudd_addApply(manager, Cudd_addMinus, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 14: /*Maximum*/
			f = Cudd_addApply(manager, Cudd_addMaximum, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 15: /*Minimum*/
			f = Cudd_addApply(manager, Cudd_addMinimum, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 16: /*Energy Subtraction*/
			retrieve_set_maxEnergy(0, 1, 0); /*do not use max energy bound*/
			f = Cudd_addApply(manager, Cudd_addEnergyMinus, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 17: /*Energy Addition*/
			f = Cudd_addApply(manager, Cudd_addEnergyPlus, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		case 18:
			f = Cudd_addApply(manager, Cudd_addXnor, d, e);
			Cudd_Ref(Cudd_Regular(f));
			break;
		default:
			die(env, "operation not supported");
			return INVALID_BDD;
		}
	}
	return f;
}

/**** START OF NATIVE METHOD IMPLEMENTATIONS ****/

JNIEXPORT jint JNICALL JNI_OnLoad(JavaVM *vm, void *reserved) {
#ifndef __linux__ 
	InitializeCriticalSection(&critSec);
#endif
	return JNI_VERSION_1_4;
}
JNIEXPORT void JNICALL JNI_OnUnload(JavaVM *vm, void *reserved) {
#ifndef __linux__ 
	DeleteCriticalSection(&critSec);
#endif
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    registerNatives
* Signature: ()V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_registerNatives
(JNIEnv *env, jclass cl)
{
	jclass cls = (*env)->FindClass(env, BDDFACTORY_CLASS_NAME);
	const char* type = "Lnet/sf/javabdd/BDDFactory$ReorderMethod;";
	JAVA_REORDER_NONE =
		(*env)->GetStaticFieldID(env, cls, "REORDER_NONE", type);
	JAVA_REORDER_RANDOM =
		(*env)->GetStaticFieldID(env, cls, "REORDER_RANDOM", type);
	JAVA_REORDER_SIFT =
		(*env)->GetStaticFieldID(env, cls, "REORDER_SIFT", type);
	JAVA_REORDER_SIFTITE =
		(*env)->GetStaticFieldID(env, cls, "REORDER_SIFTITE", type);
	JAVA_REORDER_WIN2 =
		(*env)->GetStaticFieldID(env, cls, "REORDER_WIN2", type);
	JAVA_REORDER_WIN2ITE =
		(*env)->GetStaticFieldID(env, cls, "REORDER_WIN2ITE", type);
	JAVA_REORDER_WIN3 =
		(*env)->GetStaticFieldID(env, cls, "REORDER_WIN3", type);
	JAVA_REORDER_WIN3ITE =
		(*env)->GetStaticFieldID(env, cls, "REORDER_WIN3ITE", type);
}

//typedef struct CuddPairing {
//	DdNode** table;
//	struct CuddPairing *next;
//} CuddPairing;
//
//static CuddPairing *pair_list;

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    initialize0
* Signature: (II)V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_initialize0
(JNIEnv *env, jclass cl, jint numSlots, jint cacheSize)
{
	jfieldID one_fid;
	jfieldID zero_fid;
	jfieldID add_zero_fid;
	jfieldID info_fid;

	LOCK

	if (manager != NULL) { //check if the manager has already been initialized
		UNLOCK
		return;
	}
	//at this stage (manager == NULL)
	//manager = Cudd_Init(nodenum, 0, numSlots, cachesize, 0);	
	manager = Cudd_Init(0, 0, numSlots, cacheSize, 0);
	//manager = Cudd_Init(0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
	if (manager == NULL) { //check if Cudd_Init() has failed
		UNLOCK
		die(env, "unable to initialize CUDD");
		return;
	}
	manager->out = stdout;
	bdd_one = (jlong)(intptr_cast_type)Cudd_ReadOne(manager); //bdd_one
	bdd_zero = (jlong)(intptr_cast_type)Cudd_Not(Cudd_ReadOne(manager)); //the logical zero (for BDD)
	add_zero = (jlong)(intptr_cast_type)Cudd_ReadZero(manager); //ReadZero returns the arithmetic zero (for ADD, different than logical zero)

	init_const_list(env, cl, (DdNode *)(intptr_cast_type)bdd_one, 1);
	insert_new_const(env, cl, (DdNode *)(intptr_cast_type)bdd_zero, 1);
	insert_new_const(env, cl, (DdNode *)(intptr_cast_type)add_zero, 1);
	pair_list = NULL;

	one_fid = (*env)->GetStaticFieldID(env, cl, "one", "J"); //(*env)->GetFieldID(env, cl, "one", "J");
	zero_fid = (*env)->GetStaticFieldID(env, cl, "zero", "J"); //(*env)->GetFieldID(env, cl, "zero", "J");
	add_zero_fid = (*env)->GetStaticFieldID(env, cl, "addZero", "J"); //(*env)->GetFieldID(env, cl, "addZero", "J");
	info_fid = (*env)->GetStaticFieldID(env, cl, "info", "J");
	//Add manager ID
	//initialize manager to NULL (init IDs)
	if (!one_fid || !zero_fid || !add_zero_fid || !info_fid) { //check if GetFieldID has failed
		UNLOCK
		die(env, "cannot find static field members of CUDDFactory: version mismatch ?");
		return;
	}
	(*env)->SetStaticLongField(env, cl, one_fid, bdd_one); //(*env)->SetLongField(env, cl, one_fid, bdd_one);
	(*env)->SetStaticLongField(env, cl, zero_fid, bdd_zero); //(*env)->SetLongField(env, cl, zero_fid, bdd_zero);
	(*env)->SetStaticLongField(env, cl, add_zero_fid, add_zero); //(*env)->SetLongField(env, cl, add_zero_fid, add_zero);
	(*env)->SetStaticLongField(env, cl, info_fid, (jlong)(intptr_cast_type)manager);
	//Cudd_TurnOnCountDead(manager);
	Cudd_SetLooseUpTo(manager, 0);
	Cudd_SetMaxCacheHard(manager, 0);
	//Cudd_SetMaxLive(manager, 40000000);
	//Cudd_SetMaxMemory(manager, 4294967280);
	//Cudd_DeadAreCounted(manager);
	//Cudd_EnableReorderingReporting(manager);
	Cudd_ResetStartTime(manager);
	//Cudd_AddHook(manager, cuddShrinkSubtable, CUDD_POST_REORDERING_HOOK);
	UNLOCK
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    isInitialized0
* Signature: ()Z
*/
JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_isInitialized0
(JNIEnv *env, jclass cl)
{
	LOCK
	jboolean res = (manager != NULL);
	UNLOCK
	return res;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    done0
* Signature: ()V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_done0
(JNIEnv *env, jclass cl)
{
	DdManager* m;

	LOCK

	free_gr1_mem();
	free_rabin_mem();

	int varnum = Cudd_ReadSize(manager);

	if (manager == NULL) {
		return;
	}

	while (pair_list) {
		CuddPairing *p;
		int n;
		for (n = 0; n<varnum; n++) {
			Cudd_RecursiveDeref(manager, pair_list->table[n]);
		}
		free(pair_list->table);
		p = pair_list->next;
		free(pair_list);
		pair_list = p;
	}
	free_const_list();
	
	//Cudd_DebugCheck(manager);
	//Cudd_CheckKeys(manager);
	//int refCnt = Cudd_CheckZeroRef(manager);
	//if (refCnt > 0) {
	//	//printf("The number of non freed nodes %d\n", refCnt);
	//}
	//cuddHeapProfile(manager);

	m = manager;
	manager = NULL; // race condition with delRef
	UNLOCK
	Cudd_Quit(m);
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    varNum0
* Signature: ()I
*/
JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_varNum0
(JNIEnv *env, jclass cl)
{
	return Cudd_ReadSize(manager);
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    getSize0
* Signature: (J)I
*/
JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_getSize0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode* d;
	d = (DdNode*)(intptr_cast_type)a;

	return (jint) Cudd_DagSize(d);
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    setVarNum0
* Signature: (IZ)I
*/
JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_setVarNum0
(JNIEnv *env, jclass cl, jint x, jboolean is_add)
{
	jint old = Cudd_ReadSize(manager);
	CuddPairing *p;
	DdNode *(*ithVar)(DdManager*, int) = (is_add) ? Cudd_addIthVar : Cudd_bddIthVar; //added support for ADD
	DdNode *(*newVar)(DdManager*) = (is_add) ? Cudd_addNewVar : Cudd_bddNewVar; //added support for ADD
	DdNode *new_var;
	{
		if (x < 1 || x < old || x > CUDD_MAXINDEX) {
			jclass cls = (*env)->FindClass(env, "java/lang/IllegalArgumentException");
			(*env)->ThrowNew(env, cls, "invalid number of variables");
			(*env)->DeleteLocalRef(env, cls);
			return 0;
		}
		LOCK
		p = pair_list;
		while (p) {
			int n;
			DdNode** t = (DdNode**)malloc(sizeof(DdNode*)*x);
			if (t == NULL) return 0;
			memcpy(t, p->table, sizeof(DdNode*)*old);
			for (n = old; n < x; n++) {
				//int var = n;
				//int var = Cudd_ReadInvPerm(manager, n); // level2var
				t[n] = ithVar(manager, n); //was: t[n] = ithVar(manager, var);
				Cudd_Ref(t[n]);
			}
			free(p->table);
			p->table = t;
			p = p->next;
		}
		while (Cudd_ReadSize(manager) < x) {
			new_var = newVar(manager);
			if (is_add) {
				Cudd_Ref(new_var);
			}
		}
		UNLOCK
		return old;
	}
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    ithVar0
* Signature: (IZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_ithVar0
(JNIEnv *env, jclass cl, jint i, jboolean is_add)
{
	DdNode* d;
	jlong result;
	if (i >= CUDD_MAXINDEX - 1) {
		return INVALID_BDD;
	}
	LOCK
	if (is_add) {
		d = Cudd_addIthVar(manager, i);
	}
	else {
		d = Cudd_bddIthVar(manager, i);
	}
	Cudd_Ref(d);
	result = (jlong)(intptr_cast_type)d;
	UNLOCK
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    level2Var0
* Signature: (I)I
*/
JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_level2Var0
(JNIEnv *env, jclass cl, jint level)
{
	//return manager->invperm[level];
	return (jint)Cudd_ReadInvPerm(manager, level);
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    var2Level0
* Signature: (I)I
*/
JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_var2Level0
(JNIEnv *env, jclass cl, jint v)
{
	//return (jint) cuddI(manager, v);
	return (jint)Cudd_ReadPerm(manager, v);
}

/*
* Class:     net_sf_javabdd_CUDDFactautoreorderory
* Method:    autoReorder0
* Signature: (Lnet/sf/javabdd/BDDFactory/ReorderMethod;)V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_autoReorder0
(JNIEnv *env, jclass cl, jobject javamethod, jboolean setmax, jint maxval)
{
	unsigned int unsigned_max_val;
	Cudd_ReorderingType cuddmethod = getCUDDReorderMethod(env, javamethod);
	LOCK
	if (!(*env)->ExceptionOccurred(env)) {
		if (cuddmethod == CUDD_REORDER_NONE) {
			Cudd_AutodynDisable(manager);
		}
		else {
			Cudd_AutodynEnable(manager, cuddmethod);
			if (setmax) {
				unsigned_max_val = maxval;
				if (maxval == 0x7FFFFFFF) { /*maxval equals infinity*/
					unsigned_max_val = ~0;
				}
				Cudd_SetMaxReorderings(manager, unsigned_max_val);
			}
		}
	}
	UNLOCK
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    reorder0
* Signature: (Lnet/sf/javabdd/BDDFactory/ReorderMethod;ZI)V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_reorder0
(JNIEnv *env, jclass cl, jobject javamethod)
{
	LOCK
	Cudd_ReorderingType cuddmethod = getCUDDReorderMethod(env, javamethod);
	if (!(*env)->ExceptionOccurred(env)) {
		Cudd_ReduceHeap(manager, cuddmethod, 10);
	}
	UNLOCK
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    getreordermethod0
* Signature: ()Lnet/sf/javabdd/BDDFactory/ReorderMethod;
*/
JNIEXPORT jobject JNICALL Java_net_sf_javabdd_CUDDFactory_getreordermethod0
(JNIEnv *env, jclass cl)
{

	Cudd_ReorderingType method;
	jobject java_method = NULL;
	jfieldID method_ID;

	Cudd_ReorderingStatus(manager, &method);
	method_ID = getJavaReorderMethodId(env, method);
	if (!(*env)->ExceptionOccurred(env)) {
		java_method = (*env)->GetStaticObjectField(env, cl, method_ID);
	}
	return java_method;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    autoReorder1
* Signature: ()V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_autoReorder1
(JNIEnv *env, jclass cl)
{
	LOCK
	Cudd_AutodynEnable(manager, CUDD_REORDER_SAME); /*the ordering method is left unchanged*/
	UNLOCK
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    reorderVerbose0
* Signature: (I)I
*/
JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_reorderVerbose0
(JNIEnv *env, jclass cl, jint report)
{
	jint old_level;
	LOCK
	old_level = Cudd_ReorderingReporting(manager);
	if (report) { /*report level > 0*/
		Cudd_EnableReorderingReporting(manager);
	}
	else { /*report level is 0 (i.e. no reporting at all)*/
		Cudd_DisableReorderingReporting(manager);
	}
	UNLOCK
	return old_level; /*return the previous report (verbose) level*/
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    setVarOrder0
* Signature: ([I)V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_setVarOrder0
(JNIEnv *env, jclass cl, jintArray arr)
{
	int *a;
	LOCK
	int varnum = Cudd_ReadSize(manager);
	jint size = (*env)->GetArrayLength(env, arr);
	if (size != varnum) {
		UNLOCK
		jclass cls = (*env)->FindClass(env, "java/lang/IllegalArgumentException");
		(*env)->ThrowNew(env, cls, "array size != number of vars");
		(*env)->DeleteLocalRef(env, cls);
		return;
	}
	a = (int*)(*env)->GetPrimitiveArrayCritical(env, arr, NULL);
	if (a == NULL) {
		UNLOCK
		return;
	}
	Cudd_ShuffleHeap(manager, a);
	(*env)->ReleasePrimitiveArrayCritical(env, arr, a, JNI_ABORT);
	UNLOCK
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    addVarBlock0
* Signature: (IIZ)V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_addVarBlock0
(JNIEnv *env, jclass cl, jint first, jint last, jboolean fixed)
{
	int firstp = Cudd_ReadPerm(manager, first);
	int lastp = Cudd_ReadPerm(manager, last);
	LOCK
	if (firstp <= lastp) {
		int len = lastp - firstp + 1;
		Cudd_MakeTreeNode(manager, first, len, fixed ? MTR_FIXED : MTR_DEFAULT);
	}
	else {
		UNLOCK
		die(env, "Bad indexes in variable block!");
	}
	UNLOCK
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    clearVarBlocks0
* Signature: ()V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_clearVarBlocks0
(JNIEnv *env, jclass cl)
{
	Cudd_FreeTree(manager);
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    getAllocNum0
* Signature: ()I
*/
JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_getAllocNum0
(JNIEnv *env, jclass cl)
{
	return Cudd_ReadPeakNodeCount(manager);
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    getNodeNum0
* Signature: ()I
*/
JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_getNodeNum0
(JNIEnv *env, jclass cl)
{
	return Cudd_ReadNodeCount(manager);
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    getCacheSize0
* Signature: ()I
*/
JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_getCacheSize0
(JNIEnv *env, jclass cl)
{
	return Cudd_ReadCacheSlots(manager);
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    printStat0
* Signature: ()V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_printStat0
(JNIEnv *env, jclass cl)
{
	int print_succeed;
	print_succeed = Cudd_PrintInfo(manager, stdout);
	if (!print_succeed) {
		die(env, "Cudd_PrintInfo() has failed.");
	}
}
/* class net_sf_javabdd_CUDDFactory_CUDDBDD */

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    var0
* Signature: (J)I
*/
JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_var0
(JNIEnv *env, jclass cl, jlong b)
{
	DdNode* d;
	d = (DdNode*)(intptr_cast_type)b;
	return Cudd_Regular(d)->index;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    high0
* Signature: (JZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_high0
(JNIEnv *env, jclass cl, jlong b, jboolean is_add)
{
	DdNode* d;
	DdNode* res;
	jlong result;
	LOCK
	d = (DdNode*)(intptr_cast_type)b;

	if (cuddIsConstant(d)) {
		UNLOCK
		/*jclass cls = (*env)->FindClass(env, "net/sf/javabdd/BDDException");
		(*env)->ThrowNew(env, cls, "cannot get a child of a terminal node");
		(*env)->DeleteLocalRef(env, cls);*/
		return -1;
	}
	//d is an internal node
	res = Cudd_T(d);
	if (!is_add) {
		res = Cudd_NotCond(res, Cudd_IsComplement(d));
	}
	Cudd_Ref(res);
	result = (jlong)(intptr_cast_type)res;
	UNLOCK
	return result;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    low0
* Signature: (J)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_low0
(JNIEnv *env, jclass cl, jlong b, jboolean is_add)
{
	DdNode* d;
	DdNode* res;
	jlong result;
	LOCK
	d = (DdNode*)(intptr_cast_type)b;

	if (cuddIsConstant(d)) {
		UNLOCK
		/*jclass cls = (*env)->FindClass(env, "net/sf/javabdd/BDDException");
		(*env)->ThrowNew(env, cls, "cannot get a child of a terminal node");
		(*env)->DeleteLocalRef(env, cls);*/
		return -1;
	}
	//d is an internal node
	res = Cudd_E(d);
	if (!is_add) {
		res = Cudd_NotCond(res, Cudd_IsComplement(d));
	}
	Cudd_Ref(Cudd_Regular(res));
	result = (jlong)(intptr_cast_type)res;
	UNLOCK
	return result;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    not0
* Signature: (JZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_not0
(JNIEnv *env, jclass cl, jlong b, jboolean is_add)
{
	DdNode* d;
	jlong result;
	LOCK
	d = (DdNode*)(intptr_cast_type)b;
	if (is_add) {
		d = Cudd_addCmpl(manager, d);
	}
	else {
		d = Cudd_Not(d);

	}
	Cudd_Ref(d);
	result = (jlong)(intptr_cast_type)d;
	UNLOCK
	return result;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    ite0
* Signature: (JJJZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_ite0
(JNIEnv *env, jclass cl, jlong a, jlong b, jlong c, jboolean is_add)
{
	DdNode* d;
	DdNode* e;
	DdNode* f;
	DdNode* g;
	jlong result;
	LOCK
	DdNode *(*ite)(DdManager*, DdNode*, DdNode*, DdNode*) = (is_add) ? Cudd_addIte : Cudd_bddIte;
	d = (DdNode*)(intptr_cast_type)a;
	e = (DdNode*)(intptr_cast_type)b;
	f = (DdNode*)(intptr_cast_type)c;
	g = ite(manager, d, e, f);
	Cudd_Ref(g);
	result = (jlong)(intptr_cast_type)g;
	UNLOCK
	return result;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    relprod0
* Signature: (JJJ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_relprod0
(JNIEnv *env, jclass cl, jlong a, jlong b, jlong c)
{
	DdNode* d;
	DdNode* e;
	DdNode* f;
	DdNode* g;
	jlong result;
	LOCK
	d = (DdNode*)(intptr_cast_type)a;
	e = (DdNode*)(intptr_cast_type)b;
	f = (DdNode*)(intptr_cast_type)c;
	g = Cudd_bddAndAbstract(manager, d, e, f);
	Cudd_Ref(g);
	result = (jlong)(intptr_cast_type)g;
	UNLOCK
	return result;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    compose0
* Signature: (JJIZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_compose0(JNIEnv *env, jclass cl, jlong a, jlong b, jint i, jboolean is_add)
{
	DdNode* d;
	DdNode* e;
	DdNode* f;
	jlong result;
	LOCK
	DdNode *(*compose)(DdManager*, DdNode*, DdNode*, int) = (is_add) ? Cudd_addCompose : Cudd_bddCompose;
	d = (DdNode*)(intptr_cast_type)a;
	e = (DdNode*)(intptr_cast_type)b;
	f = compose(manager, d, e, i);
	Cudd_Ref(f);
	result = (jlong)(intptr_cast_type)f;
	UNLOCK
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    addAbstractMin0
* Signature: (JJZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addAbstractMin0
(JNIEnv *env, jclass cl, jlong a, jlong b)
{
	DdNode* d;
	DdNode* e;
	DdNode* f;
	jlong result;
	LOCK
	d = (DdNode*)(intptr_cast_type)a;
	e = (DdNode*)(intptr_cast_type)b;
	f = Cudd_addMinAbstract(manager, d, e);
	Cudd_Ref(f);
	result = (jlong)(intptr_cast_type)f;
	UNLOCK
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    addAbstractMax0
* Signature: (JJZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addAbstractMax0
(JNIEnv *env, jclass cl, jlong a, jlong b)
{
	DdNode* d;
	DdNode* e;
	DdNode* f;
	jlong result;
	LOCK
	d = (DdNode*)(intptr_cast_type)a;
	e = (DdNode*)(intptr_cast_type)b;
	f = Cudd_addMaxAbstract(manager, d, e);
	Cudd_Ref(f);
	result = (jlong)(intptr_cast_type)f;
	UNLOCK
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    exist0
* Signature: (JJZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_exist0
(JNIEnv *env, jclass cl, jlong a, jlong b, jboolean is_add)
{
	DdNode* d;
	DdNode* e;
	DdNode* f;
	jlong result;
	DdNode* (*add_exist) (DdManager*, DdNode*, DdNode*) = NULL;
	LOCK
	if (is_add) {
		jboolean zero_one_add = Java_net_sf_javabdd_CUDDFactory_isZeroOneADD0(env, cl, a);
		add_exist = (zero_one_add) ? Cudd_addOrAbstract : Cudd_addExistAbstract;
	}
	DdNode* (*exist) (DdManager*, DdNode*, DdNode*) = (is_add) ? add_exist : Cudd_bddExistAbstract;
	d = (DdNode*)(intptr_cast_type)a;
	e = (DdNode*)(intptr_cast_type)b;
	f = exist(manager, d, e);
	Cudd_Ref(f);
	result = (jlong)(intptr_cast_type)f;
	UNLOCK
	return result;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    forAll0
* Signature: (JJZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_forAll0(JNIEnv *env, jclass cl, jlong a, jlong b, jboolean is_add)
{
	DdNode* d;
	DdNode* e;
	DdNode* f;
	jlong result;
	LOCK
	DdNode* (*univ) (DdManager*, DdNode*, DdNode*) = (is_add) ? Cudd_addUnivAbstract : Cudd_bddUnivAbstract;
	d = (DdNode*)(intptr_cast_type)a;
	e = (DdNode*)(intptr_cast_type)b;
	f = univ(manager, d, e);
	Cudd_Ref(f);
	result = (jlong)(intptr_cast_type)f;
	UNLOCK
	return result;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    simplify0
* Signature: (JJZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_simplify0
(JNIEnv *env, jclass cl, jlong a, jlong b, jboolean is_add)
{
	DdNode* d;
	DdNode* e;
	DdNode* f;
	jlong result;
	LOCK
	d = (DdNode*)(intptr_cast_type)a;
	e = (DdNode*)(intptr_cast_type)b;
	if (is_add) {
		f = Cudd_addRestrict(manager, d, e);
	}
	else {
		f = Cudd_bddRestrict(manager, d, e);
	}
	Cudd_Ref(f);
	result = (jlong)(intptr_cast_type)f;
	UNLOCK
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    restrict0
* Signature: (JJ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_restrict0
(JNIEnv *env, jclass cl, jlong a, jlong b)
{
	DdNode* d;
	DdNode* e;
	DdNode* f;
	jlong result;
	LOCK
	d = (DdNode*)(intptr_cast_type)a;
	e = (DdNode*)(intptr_cast_type)b;
	f = Cudd_Cofactor(manager, d, e);
	Cudd_Ref(f);
	result = (jlong)(intptr_cast_type)f;
	UNLOCK
	return result;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    restrictWith0
* Signature: (JJZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_restrictWith0
(JNIEnv *env, jclass cl, jlong a, jlong b, jboolean derefOther)
{
	DdNode *old_this_node, *old_other_node;
	jlong res;
	res = Java_net_sf_javabdd_CUDDFactory_restrict0(env, cl, a, b);
	old_this_node = (DdNode*)(intptr_cast_type)a;
	LOCK
	Cudd_RecursiveDeref(manager, Cudd_Regular(old_this_node));
	if (derefOther) {
		old_other_node = (DdNode*)(intptr_cast_type)b;
		Cudd_RecursiveDeref(manager, Cudd_Regular(old_other_node));
	}
	UNLOCK
	return res;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    support0
* Signature: (JZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_support0
(JNIEnv *env, jclass cl, jlong a, jboolean is_add)
{
	DdNode *d;
	DdNode *e, *tmp;
	jlong result;
	LOCK
	d = (DdNode*)(intptr_cast_type)a;
	e = Cudd_Support(manager, d);
	Cudd_Ref(e);
	if (is_add) {
		tmp = e;
		e = Cudd_BddToAdd(manager, tmp);
		Cudd_Ref(e);
		Cudd_RecursiveDeref(manager, tmp);
	}
	result = (jlong)(intptr_cast_type)e;
	UNLOCK
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    apply0
* Signature: (JJIZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_apply0
(JNIEnv *env, jclass cl, jlong a, jlong b, jint oper, jboolean is_add, jboolean applyWith, jboolean derefOther)
{
	jlong result;
	DdNode *old_this_node, *old_other_node, *f;
	LOCK
	f = applyOp(env, a, b, oper, is_add);
	if (applyWith) {
		old_this_node = (DdNode*)(intptr_cast_type) a;
		Cudd_RecursiveDeref(manager, Cudd_Regular(old_this_node));
		if (derefOther) {
			old_other_node = (DdNode*)(intptr_cast_type)b;
			Cudd_RecursiveDeref(manager, Cudd_Regular(old_other_node));
		}
	}
	UNLOCK
	result = (jlong)(intptr_cast_type)f;
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    logicZero0
* Signature: ()J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_logicZero0
(JNIEnv *env, jclass cl)
{

	DdNode *logicZero;
	logicZero = Cudd_ReadLogicZero(manager);
	LOCK
	Cudd_Ref(Cudd_Regular(logicZero));
	UNLOCK
	return (jlong)(intptr_cast_type)logicZero;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:   arithmeticZero0
* Signature: ()J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_arithmeticZero0
(JNIEnv *env, jclass cl)
{

	DdNode *arithmeticZero;
	arithmeticZero = Cudd_ReadZero(manager);
	LOCK
	Cudd_Ref(Cudd_Regular(arithmeticZero));
	UNLOCK
	return (jlong)(intptr_cast_type)arithmeticZero;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:  arithmeticPlusInfinity0
* Signature: ()J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_arithmeticPlusInfinity0
(JNIEnv *env, jclass cl)
{

	DdNode *plusInf;
	plusInf = Cudd_ReadPlusInfinity(manager);
	LOCK
	Cudd_Ref(Cudd_Regular(plusInf));
	UNLOCK
	return (jlong)(intptr_cast_type)plusInf;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:  arithmeticMinusInfinity0
* Signature: ()J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_arithmeticMinusInfinity0
(JNIEnv *env, jclass cl)
{

	DdNode *minusInf;
	minusInf = Cudd_ReadMinusInfinity(manager);
	LOCK
	Cudd_Ref(Cudd_Regular(minusInf));
	UNLOCK
	return (jlong)(intptr_cast_type)minusInf;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:   arithmeticLogicOne0
* Signature: ()J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_arithmeticLogicOne0
(JNIEnv *env, jclass cl) {
	DdNode *arithmeticLogicOne;
	arithmeticLogicOne = Cudd_ReadOne(manager);
	LOCK
	Cudd_Ref(Cudd_Regular(arithmeticLogicOne));
	UNLOCK
	return (jlong)(intptr_cast_type)arithmeticLogicOne;
}
static DdNode* satone_fixedVerADD(DdNode* f) {
	DdGen* first_cube;
	int *cube_arr, i;
	CUDD_VALUE_TYPE cube_val;
	DdNode *cur_cube, *one, *zero, *var, *fn;

	first_cube = Cudd_FirstCube(manager, f, &cube_arr, &cube_val);
	if (first_cube == NULL) {
		free(cube_arr);
		return NULL;
	}
	
	if (Cudd_IsGenEmpty(first_cube)) {
		return DD_ZERO(manager);
	}

	one = DD_ONE(manager);
	zero = DD_ZERO(manager);

	cur_cube = one;
	cuddRef(cur_cube);

	for (i = 0; i < manager->size; i++) {
		if (cube_arr[i] == 2) { continue; }
		cuddRef(one);
		cuddRef(zero);
		var = cuddUniqueInter(manager, i, one, zero);
		if (var == NULL) {
			Cudd_RecursiveDeref(manager, cur_cube);
			return NULL;
		}
		cuddRef(var);
		cuddDeref(one);

		if (cube_arr[i] == 1) { //positive (not a dont care)
			fn = Cudd_addIte(manager, var, cur_cube, zero);
		}
		else if (cube_arr[i] == 0) { //negative
			fn = Cudd_addIte(manager, var, zero, cur_cube);
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

	Cudd_GenFree(first_cube);
	return cur_cube;
}

/*this method is valid only for 0-1 ADD; f is assumed to be a 0-1 ADD*/
/*this method needs to be fixed to support the case when auto reordering occurs*/
static DdNode* satone_zeroOneADD_rec(DdNode* f)
{
	DdNode* zero = (DdNode*)(intptr_cast_type)add_zero;
	DdNode* one = (DdNode*)(intptr_cast_type)bdd_one;
	DdNode* F = Cudd_Regular(f);
	DdNode* high;
	DdNode* low;
	DdNode* r;
	unsigned int index;

	if (F == zero ||
		F == one) {
		return f;
	}

	index = F->index;
	high = cuddT(F);
	low = cuddE(F);
	//if (Cudd_IsComplement(f)) {
	//	high = Cudd_Not(high);
	//	low = Cudd_Not(low);
	//}
	if (low == (DdNode*)(intptr_cast_type)add_zero) {
		DdNode* res = satone_zeroOneADD_rec(high);
		if (res == NULL) {
			return NULL;
		}
		cuddRef(res);
		//if (Cudd_IsComplement(res)) {
		//	r = cuddUniqueInter(manager, (int)index, Cudd_Not(res), one);
		//	if (r == NULL) {
		//		Cudd_RecursiveDeref(manager, res);
		//		return NULL;
		//	}
		//	r = Cudd_Not(r);
		//}
		//else {
		r = cuddUniqueInter(manager, (int)index, res, zero);
		if (r == NULL) {
			Cudd_RecursiveDeref(manager, res);
			return NULL;
		}
		//}
		cuddDeref(res);
	}
	else {
		DdNode* res = satone_zeroOneADD_rec(low);
		if (res == NULL) return NULL;
		cuddRef(res);
		r = cuddUniqueInter(manager, (int)index, zero, res);
		if (r == NULL) {
			Cudd_RecursiveDeref(manager, res);
			return NULL;
		}
		//r = Cudd_Not(r);
		cuddDeref(res);
	}

	return r;
}


static DdNode* satone_rec(DdNode* f)
{
	DdNode* zero = (DdNode*)(intptr_cast_type)bdd_zero;
	DdNode* one = (DdNode*)(intptr_cast_type)bdd_one;
	DdNode* F = Cudd_Regular(f);
	DdNode* high;
	DdNode* low;
	DdNode* r;
	unsigned int index;

	if (F == zero ||
		F == one) {
		return f;
	}

	index = F->index;
	high = cuddT(F);
	low = cuddE(F);
	if (Cudd_IsComplement(f)) {
		high = Cudd_Not(high);
		low = Cudd_Not(low);
	}
	if (low == (DdNode*)(intptr_cast_type)bdd_zero) {
		DdNode* res = satone_rec(high);
		if (res == NULL) {
			return NULL;
		}
		cuddRef(res);
		if (Cudd_IsComplement(res)) {
			r = cuddUniqueInter(manager, (int)index, Cudd_Not(res), one);
			if (r == NULL) {
				LOCK
				Cudd_IterDerefBdd(manager, res);
				UNLOCK
				return NULL;
			}
			r = Cudd_Not(r);
		}
		else {
			r = cuddUniqueInter(manager, (int)index, res, zero);
			if (r == NULL) {
				LOCK
				Cudd_IterDerefBdd(manager, res);
				UNLOCK
				return NULL;
			}
		}
		LOCK
		cuddDeref(res);
		UNLOCK
	}
	else {
		DdNode* res = satone_rec(low);
		if (res == NULL) return NULL;
		LOCK
		cuddRef(res);
		UNLOCK
		r = cuddUniqueInter(manager, (int)index, one, Cudd_Not(res));
		if (r == NULL) {
			LOCK
			Cudd_IterDerefBdd(manager, res);
			UNLOCK
			return NULL;
		}
		r = Cudd_Not(r);
		LOCK
		cuddDeref(res);
		UNLOCK
	}

	return r;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    satOne0
* Signature: (J)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_satOne0
(JNIEnv *env, jclass cl, jlong a, jboolean is_add)
{
	DdNode* d;
	DdNode* res;
	jlong result;

	d = (DdNode*)(intptr_cast_type)a;

	/*
	if (is_add && !Java_net_sf_javabdd_CUDDFactory_isZeroOneADD0(env, cl, a)) {
		jclass cls = (*env)->FindClass(env, "net/sf/javabdd/BDDException");
		(*env)->ThrowNew(env, cls, "Cannot find a satisfying variable assignment for a non 0-1 ADD");
		(*env)->DeleteLocalRef(env, cls);
		return 0;
	}
	*/

	DdNode* (*satone)(DdNode*) = (is_add) ? satone_fixedVerADD : satone_rec; //satone_zeroOneADD_rec

	LOCK
	do {
		manager->reordered = 0;
		res = satone(d);
	} while (manager->reordered == 1); //CHECK DEREF ISSUES IN THIS LOOP
	Cudd_Ref(res);
	UNLOCK
	result = (jlong)(intptr_cast_type)res;
	return result;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    nodeCount0
* Signature: (J)I
*/
JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_nodeCount0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode* d;
	d = (DdNode*)(intptr_cast_type)a;
	return Cudd_DagSize(d) - 1;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    pathCount0
* Signature: (J)D
*/
JNIEXPORT jdouble JNICALL Java_net_sf_javabdd_CUDDFactory_pathCount0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode* d;
	d = (DdNode*)(intptr_cast_type)a;
	return Cudd_CountPathsToNonZero(d);
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    satCount0
* Signature: (J)D
*/
JNIEXPORT jdouble JNICALL Java_net_sf_javabdd_CUDDFactory_satCount0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode* d;
	int varcount = Cudd_ReadSize(manager);
	d = (DdNode*)(intptr_cast_type)a;
	return Cudd_CountMinterm(manager, d, varcount);
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    addRef
* Signature: (J)V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_addRef
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode* d;
	//Cudd_DebugCheck(manager);
	//Cudd_CheckKeys(manager);
	if (a == (-1)) { return; }
	LOCK
	if (manager == NULL) {
		UNLOCK
		return; 
	}
	d = (DdNode*)(intptr_cast_type)a;
	if (d != INVALID_BDD) {
		Cudd_Ref(d);
	}
	UNLOCK
	//Cudd_DebugCheck(manager);
	//Cudd_CheckKeys(manager);
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    delRef
* Signature: (J)V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_delRef
(JNIEnv *env, jclass cl, jlong a, jboolean is_add)
{
	DdNode* d;
	LOCK
	if (manager == NULL) {
		UNLOCK
		return;
	}
	if (a == (-1)) {
		UNLOCK
		return;
	}
	d = (DdNode*)(intptr_cast_type)a;
	//Cudd_DebugCheck(manager);
	//Cudd_CheckKeys(manager);
	if (d != INVALID_BDD) {
		if (d == DD_ONE(manager) || d == Cudd_Not(DD_ONE(manager)) || d == DD_ZERO(manager)) {
			if (d->ref <= 1) {
				UNLOCK
				return; 
			}
		}
		if (d->ref > 0) {
			if (is_add) {
				Cudd_RecursiveDeref(manager, d);
			}
			else {
				Cudd_IterDerefBdd(manager, d);
			}
		}
	}
	UNLOCK
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    veccompose0
* Signature: (JJZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_veccompose0
(JNIEnv *env, jclass cl, jlong a, jlong b, jboolean is_add)
{
	DdNode* d;
	CuddPairing* e;
	DdNode* f;
	jlong result;
	DdNode*(*compose)(DdManager*, DdNode*, DdNode**) = (is_add) ? Cudd_addVectorCompose : Cudd_bddVectorCompose;
	d = (DdNode*)(intptr_cast_type)a;
	e = (CuddPairing*)(intptr_cast_type)b;
	LOCK
	f = compose(manager, d, e->table);
	Cudd_Ref(f);
	UNLOCK
	result = (jlong)(intptr_cast_type)f;
	return result;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    replace0
* Signature: (JJZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_replace0
(JNIEnv *env, jclass cl, jlong a, jlong b, jboolean is_add)
{
	DdNode* d;
	CuddPairing* e;
	DdNode* f;
	jlong result;
	int n;
	unsigned int *arr;
	DdNode*(*permute)(DdManager*, DdNode*, int*) = (is_add) ? Cudd_addPermute : Cudd_bddPermute;
	int varnum = Cudd_ReadSize(manager);
	arr = (unsigned int*)malloc(sizeof(unsigned int)*varnum);
	if (arr == NULL) {
		jclass cls = (*env)->FindClass(env, "net/sf/javabdd/BDDException");
		(*env)->ThrowNew(env, cls, "replace0() method error: malloc() of the new permutation array has failed");
		(*env)->DeleteLocalRef(env, cls);
		return INVALID_BDD;
	}
	d = (DdNode*)(intptr_cast_type)a;
	e = (CuddPairing*)(intptr_cast_type)b;
	for (n = 0; n<varnum; ++n) {
		DdNode* node = e->table[n];
		unsigned int var = Cudd_NodeReadIndex(node);
		arr[n] = var;
		//int var = node->index; //Cudd_Regular(node)->index;
		//int level = var;
		//int level = Cudd_ReadPerm(manager, var);

	}
	LOCK
	f = permute(manager, d, arr);
	Cudd_Ref(f);
	UNLOCK
	free(arr);
	result = (jlong)(intptr_cast_type)f;
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    replaceWith0
* Signature: (JJZ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_replaceWith0
(JNIEnv *env, jclass cl, jlong a, jlong b, jboolean is_add)
{
	DdNode *old_this_node;
	jlong res;
	res = Java_net_sf_javabdd_CUDDFactory_replace0(env, cl, a, b, is_add);
	old_this_node = (DdNode*)(intptr_cast_type)a;
	LOCK
	Cudd_RecursiveDeref(manager, Cudd_Regular(old_this_node));
	UNLOCK
	return res;
}


/* class net_sf_javabdd_CUDDFactory_CUDDBDDPairing */

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    alloc
* Signature: (Z)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_alloc
(JNIEnv *env, jclass cl, jboolean is_add)
{
	int n;
	int varnum = Cudd_ReadSize(manager);
	CuddPairing* r = (CuddPairing*)malloc(sizeof(CuddPairing));
	if (r == NULL) return 0;
	r->table = (DdNode**)malloc(sizeof(DdNode*)*varnum);
	if (r->table == NULL) {
		free(r);
		return 0;
	}
	DdNode *(*ithVar)(DdManager*, int) = (is_add) ? Cudd_addIthVar : Cudd_bddIthVar; //added support for ADD
	LOCK
	for (n = 0; n<varnum; n++) {
		int var = n;
		//int var = Cudd_ReadInvPerm(manager, n); // level2var
		r->table[n] = ithVar(manager, var);
		Cudd_Ref(r->table[n]);
	}
	r->next = pair_list;
	pair_list = r;
	UNLOCK
	return (jlong)(intptr_cast_type)r;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    set0
* Signature: (JIIZ)V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_set0
(JNIEnv *env, jclass cl, jlong p, jint var, jint b, jboolean is_add)
{
	CuddPairing* r = (CuddPairing*)(intptr_cast_type)p;
	int level1 = var;
	DdNode *(*ithVar)(DdManager*, int) = (is_add) ? Cudd_addIthVar : Cudd_bddIthVar; //added support for ADD
	//int level1 = Cudd_ReadPerm(manager, var);
	//int level2 = Cudd_ReadPerm(manager, b);
	LOCK
	Cudd_RecursiveDeref(manager, r->table[level1]);
	r->table[level1] = ithVar(manager, b);
	Cudd_Ref(r->table[level1]);
	UNLOCK
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    set2
* Signature: (JIJ)V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_set2
(JNIEnv *env, jclass cl, jlong p, jint var, jlong b)
{
	CuddPairing* r = (CuddPairing*)(intptr_cast_type)p;
	DdNode *d = (DdNode*)(intptr_cast_type)b;
	int level1 = var;
	//int level1 = Cudd_ReadPerm(manager, var);
	LOCK
	Cudd_RecursiveDeref(manager, r->table[level1]);
	r->table[level1] = d;
	Cudd_Ref(r->table[level1]);
	UNLOCK
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    reset0
* Signature: (JZ)V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_reset0
(JNIEnv *env, jclass cl, jlong p, jboolean is_add)
{
	int n;
	CuddPairing* r = (CuddPairing*)(intptr_cast_type)p;
	DdNode *(*ithVar)(DdManager*, int) = (is_add) ? Cudd_addIthVar : Cudd_bddIthVar; //added support for ADD
	int varnum = Cudd_ReadSize(manager);
	LOCK
	for (n = 0; n<varnum; n++) {
		int var;
		Cudd_RecursiveDeref(manager, r->table[n]);
		var = n;
		//int var = Cudd_ReadInvPerm(manager, n); // level2var
		r->table[n] = ithVar(manager, var);
		Cudd_Ref(r->table[n]);
	}
	UNLOCK
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    free0
* Signature: (J)V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_free0
(JNIEnv *env, jclass cl, jlong p)
{
	int n;
	CuddPairing* r = (CuddPairing*)(intptr_cast_type)p;
	CuddPairing** ptr;
	int varnum = Cudd_ReadSize(manager);
	LOCK
	for (n = 0; n<varnum; n++) {
		Cudd_RecursiveDeref(manager, r->table[n]);
	}
	ptr = &pair_list;
	while (*ptr != r)
		ptr = &(*ptr)->next;
	*ptr = r->next;
	free(r->table);
	free(r);
	UNLOCK
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    isZeroOneADD0
* Signature: (J)Z
*/
JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_isZeroOneADD0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode *f, *max, *min;

	f = (DdNode*)(intptr_cast_type)a;
	max = Cudd_addFindMax(manager, f);
	min = Cudd_addFindMin(manager, f);
	return ((max == DD_ONE(manager) || max == DD_ZERO(manager)) && (min == DD_ONE(manager) || min == DD_ZERO(manager)));
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    addConst0
* Signature: (D)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addConst0
(JNIEnv *env, jclass cl, jdouble val)
{
	DdNode *f;
	jlong result;
	CUDD_VALUE_TYPE value = (CUDD_VALUE_TYPE)val;
	LOCK
	f = Cudd_addConst(manager, value);
	Cudd_Ref(f);
	UNLOCK
	result = (jlong)(intptr_cast_type)f;
	return result;
}


/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    isAddConst0
* Signature: (J)Z
*/
JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_isAddConst0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode *d;

	d = (DdNode*)(intptr_cast_type)a;
	return (jboolean)Cudd_IsConstant(d);
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    addFindMax0
* Signature: (J)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addFindMax0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode *d, *r;
	jlong result;

	d = (DdNode*)(intptr_cast_type)a;
	LOCK
	r = Cudd_addFindMax(manager, d);
	Cudd_Ref(r);
	UNLOCK
	result = (jlong)(intptr_cast_type)r;
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    toADD0
* Signature: (J)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_toADD0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode *d, *r;
	jlong result;

	d = (DdNode*)(intptr_cast_type)a;
	LOCK
	r = Cudd_BddToAdd(manager, d);
	Cudd_Ref(r);
	UNLOCK
	result = (jlong)(intptr_cast_type)r;
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    toBDD0
* Signature: (J)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_toBDD0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode *d, *r;
	jlong result;

	d = (DdNode*)(intptr_cast_type)a;
	LOCK
	r = Cudd_addBddPattern(manager, d);
	Cudd_Ref(r);
	UNLOCK
	result = (jlong)(intptr_cast_type)r;
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    toBDDThreshold
* Signature: (J,D)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_toBDDThreshold
(JNIEnv *env, jclass cl, jlong a, jdouble b)
{
	DdNode *d, *r;
	jlong result;

	d = (DdNode*)(intptr_cast_type)a;
	LOCK
	r = Cudd_addBddThreshold(manager, d, (CUDD_VALUE_TYPE)b);
	Cudd_Ref(r);
	UNLOCK
	result = (jlong)(intptr_cast_type)r;
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    toBDDStrictThreshold
* Signature: (JD)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_toBDDStrictThreshold
(JNIEnv *env, jclass cl, jlong a, jdouble b)
{
	DdNode *d, *r;
	jlong result;

	d = (DdNode*)(intptr_cast_type)a;
	LOCK
	r = Cudd_addBddStrictThreshold(manager, d, (CUDD_VALUE_TYPE)b);
	Cudd_Ref(r);
	UNLOCK
	result = (jlong)(intptr_cast_type)r;
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    toBDDInterval
* Signature: (JDD)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_toBDDInterval
(JNIEnv *env, jclass cl, jlong a, jdouble lower, jdouble upper)
{
	DdNode *d, *r;
	jlong result;

	d = (DdNode*)(intptr_cast_type)a;
	LOCK
	r = Cudd_addBddInterval(manager, d, (CUDD_VALUE_TYPE)lower, (CUDD_VALUE_TYPE)upper);
	Cudd_Ref(r);
	UNLOCK
	result = (jlong)(intptr_cast_type)r;
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    toBDDIthBit
* Signature: (JI)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_toBDDIthBit
(JNIEnv *env, jclass cl, jlong a, jint bit)
{
	DdNode *d, *r;
	jlong result;

	d = (DdNode*)(intptr_cast_type)a;
	LOCK
	r = Cudd_addBddIthBit(manager, d, (int)bit);
	Cudd_Ref(r);
	UNLOCK
	result = (jlong)(intptr_cast_type)r;
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    addFindMin0
* Signature: (J)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addFindMin0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode *d, *r;
	jlong result;
	d = (DdNode*)(intptr_cast_type)a;
	LOCK
	r = Cudd_addFindMin(manager, d);
	Cudd_Ref(r);
	UNLOCK
	result = (jlong)(intptr_cast_type)r;
	return result;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    retrieveConstValue0
* Signature: (J)D
*/
JNIEXPORT jdouble JNICALL Java_net_sf_javabdd_CUDDFactory_retrieveConstValue0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode *d;

	d = (DdNode*)(intptr_cast_type)a;
	return (cuddV(d));
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    addAdditiveNeg0
* Signature: (J)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addAdditiveNeg0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode *d, *r;
	d = (DdNode*)(intptr_cast_type)a;
	LOCK
	r = Cudd_addNegate(manager, d);
	Cudd_Ref(r);
	UNLOCK
	return (jlong)(intptr_cast_type)r;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    addApplyLog0
* Signature: (J)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addApplyLog0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode *d, *r;
	d = (DdNode*)(intptr_cast_type)a;
	LOCK
	r = Cudd_addMonadicApply(manager, Cudd_addLog, d);
	Cudd_Ref(r);
	UNLOCK
	return (jlong)(intptr_cast_type)r;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    addMinimizeVal0
* Signature: (J)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addMinimizeVal0
(JNIEnv *env, jclass cl, jlong a, jdouble val)
{
	DdNode *d, *r;
	d = (DdNode*)(intptr_cast_type)a;
	LOCK
	retrieve_set_value((CUDD_VALUE_TYPE)val, 1);
	r = Cudd_addMonadicApply(manager, Cudd_addMinimizeVal, d);
	Cudd_Ref(r);
	UNLOCK
	return (jlong)(intptr_cast_type)r;
}
/*
* Class:   net_sf_javabdd_CUDDFactory
* Method : varSupportIndex0
* Signature : (J)[I
*/

JNIEXPORT jintArray JNICALL Java_net_sf_javabdd_CUDDFactory_varSupportIndex0
(JNIEnv *env, jclass cl, jlong a) {

	DdNode *d;
	int *r;
	LOCK
	jintArray intJavaArray = (*env)->NewIntArray(env, manager->size);
	d = (DdNode*)(intptr_cast_type)a;
	r = Cudd_SupportIndex(manager, d);
	(*env)->SetIntArrayRegion(env, intJavaArray, 0, manager->size, r);
	UNLOCK
	return intJavaArray;
}

/*
* Class:   net_sf_javabdd_CUDDFactory
* Method : printSet0
* Signature : (JI)V
*/

JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_printSet0
(JNIEnv *env, jclass cl, jlong a, jint print_stats) {

	DdNode *d;
	d = (DdNode*)(intptr_cast_type)a;
	int var_size = Cudd_SupportSize(manager, d);
	Cudd_PrintDebug(manager, d, var_size, print_stats);
}
/*
* Class:   net_sf_javabdd_CUDDFactory
* Method : reorderTimes0
* Signature : (JI)V
*/
JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_reorderTimes0
(JNIEnv *env, jclass cl) {
	jint result;
	result = (jint) Cudd_ReadReorderingTime(manager);
	return result;
}
/*
* Class:   net_sf_javabdd_CUDDFactory
* Method : printVarTree0
* Signature : (JI)V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_printVarTree0
(JNIEnv *env, jclass cl) {
	Cudd_PrintGroupedOrder(manager, "BDD", NULL);
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    addEngSubtract0
* Signature: (J)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addEngSubtract0
(JNIEnv *env, jclass cl, jlong a, jlong b, jdouble val)
{
	DdNode *r, *this_add, *that_add;
	this_add = (DdNode*)(intptr_cast_type)a;
	that_add = (DdNode*)(intptr_cast_type)b;
	LOCK
	retrieve_set_maxEnergy((CUDD_VALUE_TYPE)val, 1, 1); /*use max energy bound*/
	r = Cudd_addApply(manager, Cudd_addEnergyMinus, this_add, that_add);
	Cudd_Ref(r);
	UNLOCK
	return (jlong)(intptr_cast_type)r;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    convertToZeroOneADDByThres0
* Signature: (J)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_convertToZeroOneADDByThres0
(JNIEnv *env, jclass cl, jlong a, jlong type, jdouble val)
{
	DdNode *r, *this_add;
	this_add = (DdNode*)(intptr_cast_type)a;
	LOCK
	//retrieve_set_threshold((CUDD_VALUE_TYPE)val, 1); /*set threhold*/
	switch (type) {
	case 1: /*Strictly less-then*/
		//r = Cudd_addMonadicApply(manager, Cudd_addToZeroOnebyThresholdSLT, this_add);
		r = Cudd_addZeroOneAddSLT(manager, this_add, val);
		break;
	case 2: /*Strictly greater-then*/
		//r = Cudd_addMonadicApply(manager, Cudd_addToZeroOnebyThresholdSGT, this_add);
		r = Cudd_addZeroOneAddSGT(manager, this_add, val);
		break;
	case 3: /*less-then*/
		//r = Cudd_addMonadicApply(manager, Cudd_addToZeroOnebyThresholdLT, this_add);
		r = Cudd_addZeroOneAddLT(manager, this_add, val);
		break;
	case 4: /*greater-then*/
		//r = Cudd_addMonadicApply(manager, Cudd_addToZeroOnebyThresholdGT, this_add);
		r = Cudd_addZeroOneAddGT(manager, this_add, val);
		break;
	default:
		die(env, "operation not supported");
		return INVALID_BDD;
	}
	Cudd_Ref(r);
	UNLOCK
	return (jlong)(intptr_cast_type)r;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    printDot0
* Signature: (J)V
*/
JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_printDot0
(JNIEnv *env, jclass cl, jlong a)
{
	DdNode *this_add;
	this_add = (DdNode*)(intptr_cast_type)a;
	LOCK
	//Cudd_addMonadicApply(manager, Cudd_addPrintTerminal, this_add);
	//f//printf(manager->out, "%s", "\n");
	cuddP(manager, this_add);
	//Cudd_PrintMinterm(manager, this_add);
	UNLOCK
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    arithmeticExist0
* Signature: (JJ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_arithmeticExist0
(JNIEnv *env, jclass cl, jlong a, jlong b)
{
	DdNode* d;
	DdNode* e;
	DdNode* f;
	jlong result;
	LOCK
	d = (DdNode*)(intptr_cast_type)a;
	e = (DdNode*)(intptr_cast_type)b;
	f = Cudd_addExistAbstract(manager, d, e);
	Cudd_Ref(f);
	result = (jlong)(intptr_cast_type)f;
	UNLOCK
	return result;
}

/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    determinizeController0
* Signature: (JJ)J
*/
JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_determinizeController0
(JNIEnv *env, jclass cl, jlong a, jlong b, jboolean is_add) //a = this 0-1 ADD, b = primed system vars
{
	DdNode* d;
	DdNode* e;
	DdNode* f;
	jlong result;
	DdNode *(*determinizeController)(DdManager*, DdNode*, DdNode*) = (is_add) ? Cudd_addDeterminizeController : Cudd_bddDeterminizeController;
	LOCK
	d = (DdNode*)(intptr_cast_type)a;
	e = (DdNode*)(intptr_cast_type)b;
	f = determinizeController(manager, d, e);
	Cudd_Ref(f);
	result = (jlong)(intptr_cast_type)f;
	UNLOCK
	return result;
}
/*
* Class:     net_sf_javabdd_CUDDFactory
* Method:    negCycleCheck0
* Signature: (JJJJ)Z
*/
JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_negCycleCheck0
(JNIEnv *env, jclass cl, jlong a, jlong s, jlong v, jlong p) {

	DdNode* A;
	DdNode* S;
	DdNode* primedVars;

	CuddPairing* primedToUnprimed;
	jboolean res;
	int i;
	primedToUnprimed = (CuddPairing*)(intptr_cast_type)p;
	A = (DdNode*)(intptr_cast_type)a;
	S = (DdNode*)(intptr_cast_type)s;
	primedVars = (DdNode*)(intptr_cast_type)v;
	for (i = 0; i < manager->size; i++) {
		//printf("%d\n", primedToUnprimed->table[i]->index);
	}
	LOCK
	
	res = (jboolean) Cudd_addBellmanFord(manager, A, S, primedVars, primedToUnprimed->table);
	
	UNLOCK
	return res;
}

JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_equalBDDs0
(JNIEnv *env, jclass cl, jlong jbdd1, jlong jbdd2)
{
	jboolean res;

	DdNode* bdd1;
	DdNode* bdd2;

	bdd1 = (DdNode*)(intptr_cast_type)jbdd1;
	bdd2 = (DdNode*)(intptr_cast_type)jbdd2;

	int equal = IS_BDD_EQ(bdd1, bdd2);
	res = (jboolean)equal;
	
	return res;
}

/*
* Class: net_sf_javabdd_CUDDFactory
* GR1 game related functions
*/

JNIEXPORT jintArray JNICALL Java_net_sf_javabdd_CUDDFactory_getAttrSizes0
(JNIEnv *env, jclass cl)
{
	LOCK
	//TODO: TMP
	for (int j = 0; j < gr1_mem.sizeD1; j++)
	{
		if (gr1_mem.sizeD3[j] == -1)
		{
			//printf("getAttrSizes0: gr1_mem.sizeD3[%d] = -1 ---> ok only for inc alg\n", j);
			gr1_mem.sizeD3[j] = 0;
		}
	}

	jintArray intJavaArray = (*env)->NewIntArray(env, gr1_mem.sizeD1);
	(*env)->SetIntArrayRegion(env, intJavaArray, 0, gr1_mem.sizeD1, gr1_mem.sizeD3);

	UNLOCK
	return intJavaArray;
}

JNIEXPORT jlongArray JNICALL Java_net_sf_javabdd_CUDDFactory_getXMem0
(JNIEnv *env, jclass cl)
{
	LOCK
	int j = 0, i, cy;
	int sumD3 = 0;

	//TODO: TMP
	for (j = 0; j < gr1_mem.sizeD1; j++)
	{	
		if (gr1_mem.sizeD3[j] == -1)
		{
			//printf("getXMem0: gr1_mem.sizeD3[%d] = -1 ---> ok only for inc alg\n", j);
			gr1_mem.sizeD3[j] = 0;
		}
	}

	for (j = 0; j < gr1_mem.sizeD1; j++)
	{
		sumD3 += gr1_mem.sizeD3[j];
	}

	int retSize = gr1_mem.sizeD2*sumD3;
	intptr_cast_type * x_memRet = malloc(retSize * sizeof(intptr_cast_type));

	int idx = 0;
	for (j = 0; j < gr1_mem.sizeD1; j++)
	{
		for (i = 0; i < gr1_mem.sizeD2; i++)
		{
			for (cy = 0; cy < gr1_mem.sizeD3[j]; cy++)
			{
				x_memRet[idx] = (intptr_cast_type)gr1_mem.x_mem[j][i][cy];
				idx++;
			}
		}
	}

	jlongArray longJavaArray = (*env)->NewLongArray(env, retSize);
	(*env)->SetLongArrayRegion(env, longJavaArray, 0, retSize, x_memRet);

	free(x_memRet);
	UNLOCK
	return longJavaArray;
}

JNIEXPORT jlongArray JNICALL Java_net_sf_javabdd_CUDDFactory_getYMem0
(JNIEnv *env, jclass cl)
{
	LOCK
	int j = 0, i, cy;
	int sumD3 = 0;

	//TODO: TMP
	for (j = 0; j < gr1_mem.sizeD1; j++)
	{
		if (gr1_mem.sizeD3[j] == -1)
		{
			//printf("getYMem0: gr1_mem.sizeD3[%d] = -1 ---> ok only for inc alg\n", j);
			gr1_mem.sizeD3[j] = 0;
		}
	}

	for (j = 0; j < gr1_mem.sizeD1; j++)
	{
		sumD3 += gr1_mem.sizeD3[j];
	}

	intptr_cast_type * y_memRet = malloc(sumD3 * sizeof(intptr_cast_type));

	int idx = 0;
	for (j = 0; j < gr1_mem.sizeD1; j++)
	{
		for (cy = 0; cy < gr1_mem.sizeD3[j]; cy++)
		{
			y_memRet[idx] = (intptr_cast_type)gr1_mem.y_mem[j][cy];
			idx++;
		}
	}

	jlongArray longJavaArray = (*env)->NewLongArray(env, sumD3);
	(*env)->SetLongArrayRegion(env, longJavaArray, 0, sumD3, y_memRet);

	free(y_memRet);
	UNLOCK
	return longJavaArray;
}

JNIEXPORT jlongArray JNICALL Java_net_sf_javabdd_CUDDFactory_getZMem0
(JNIEnv *env, jclass cl)
{
	LOCK
	intptr_cast_type * z_memRet = malloc(gr1_mem.sizeD1 * sizeof(intptr_cast_type));
	for (int j = 0; j < gr1_mem.sizeD1; j++)
	{
		z_memRet[j] = (intptr_cast_type)gr1_mem.z_mem[j];
	}

	jlongArray longJavaArray = (*env)->NewLongArray(env, gr1_mem.sizeD1);
	(*env)->SetLongArrayRegion(env, longJavaArray, 0, gr1_mem.sizeD1, z_memRet);

	free(z_memRet);
	UNLOCK
	return longJavaArray;
}

JNIEXPORT jlongArray JNICALL Java_net_sf_javabdd_CUDDFactory_getZMemFirstItr0
(JNIEnv *env, jclass cl)
{
	LOCK

	intptr_cast_type * z_memRet = malloc(gr1_mem.sizeD1 * sizeof(intptr_cast_type));
	for (int j = 0; j < gr1_mem.sizeD1; j++)
	{
		z_memRet[j] = (intptr_cast_type)gr1_mem.z_mem_first_itr[j];
	}

	jlongArray longJavaArray = (*env)->NewLongArray(env, gr1_mem.sizeD1);
	(*env)->SetLongArrayRegion(env, longJavaArray, 0, gr1_mem.sizeD1, z_memRet);

	free(z_memRet);
	UNLOCK
	return longJavaArray;
}

JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_gr1Game0
(JNIEnv *env, jclass cl, jlongArray jSysJ, jlongArray jEnvJ, 
	jlong jsysIni, jlong jenvIni, jlong jSysTrans, jlong jEnvTrans,
	jlong jsysUnprime, jlong jenvUnprime, jlong jSysPrime, jlong jEnvPrime, jlong jPairs,
	jlongArray jsysTransList, jlongArray jenvTransList, jlongArray jsysQuantSets, jlongArray jenvQuantSets,
	jboolean efp, jboolean eun, jboolean fpr, jboolean sca)
{
	LOCK

	int sysJSize = (int)(*env)->GetArrayLength(env, jSysJ);
	int envJSize = (int)(*env)->GetArrayLength(env, jEnvJ);
	//printf("sysJSize = %d\n", sysJSize);
	//printf("envJSize = %d\n", envJSize);
	DdNode** sysJ = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jSysJ, NULL);
	if (sysJ == NULL) {
		//printf("sysJ is NULL\n");
		fflush(stdout);
		UNLOCK
		return -1;
	}

	DdNode** envJ = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jEnvJ, NULL);
	if (envJ == NULL) {
		//printf("envJ is NULL\n");
		fflush(stdout);
		UNLOCK
		return -1;
	}
	
	int varnum = Cudd_ReadSize(manager);
	//printf("varnum = %d\n", varnum); 

	#ifdef DD_STATS
	//printf("using DD_STATS!!!! \n");
	#endif
	CuddPairing* pairs = (CuddPairing*)(intptr_cast_type)jPairs;
	////printf("jPairs = %ld\n", jPairs); fflush(stdout);
	////printf("pair_list = %ld\n",pair_list); fflush(stdout);

	/*int n;
	for (n = 0; n < varnum; ++n) {
	DdNode* node = pairs->table[n];
	unsigned int var = Cudd_NodeReadIndex(node);
	//printf("pair(%d) = %d\n", n, var);
	}*/

	DdNode* sysTrans = (DdNode*)(intptr_cast_type)jSysTrans;
	DdNode* envTrans = (DdNode*)(intptr_cast_type)jEnvTrans;
	DdNode* sysPrimeVars = (DdNode*)(intptr_cast_type)jSysPrime;
	DdNode* envPrimeVars = (DdNode*)(intptr_cast_type)jEnvPrime;

	DdNode* sysIni = (DdNode*)(intptr_cast_type)jsysIni;
	DdNode* envIni = (DdNode*)(intptr_cast_type)jenvIni;
	DdNode* sysUnprime = (DdNode*)(intptr_cast_type)jsysUnprime;
	DdNode* envUnprime = (DdNode*)(intptr_cast_type)jenvUnprime;

	////printf("sysTrans = %d\n", sysTrans->index);
	////printf("envTrans = %d\n", envTrans->index);
	////printf("sysPrimeVars = %d\n", sysPrimeVars->index);
	////printf("envPrimeVars = %d\n", envPrimeVars->index);

	//DdNode* yieldStates = yield(Cudd_Not(Cudd_ReadOne(manager)), sysPrimeVars, envPrimeVars, pairs, sysTrans, envTrans);
	////printf("yieldStates = %d\n", yieldStates->index);

	int sysTransListSize = (int)(*env)->GetArrayLength(env, jsysTransList);
	int envTransListSize = (int)(*env)->GetArrayLength(env, jenvTransList);
	int sysQuantSetsSize = (int)(*env)->GetArrayLength(env, jsysQuantSets);
	int envQuantSetsSize = (int)(*env)->GetArrayLength(env, jenvQuantSets);
	//printf("sysTransListSize = %d\n", sysTransListSize);
	//printf("envTransListSize = %d\n", envTransListSize);
	//printf("sysQuantSetsSize = %d\n", sysQuantSetsSize);
	//printf("envQuantSetsSize = %d\n", envQuantSetsSize);

	if (sysTransListSize != sysQuantSetsSize || envTransListSize != envQuantSetsSize) {
		//printf("TransListSize != QuantSetsSize (for sys or env)\n");
		fflush(stdout);
		UNLOCK
		return -1;
	}

	if (sca) {
		//printf("simultaneous conjuction and abstraction: use Cudd_bddAndAbstract\n");
	}
	if (sysTransListSize == 0 || envTransListSize == 0) {
		//printf("not given trans-quantsets lists, will use original yield\n");
		sys_trans_quant_list.isInit = false;
		env_trans_quant_list.isInit = false;
	}
	else {
		//printf("given trans-quantsets lists, will use the decomposition yield\n");
		sys_trans_quant_list.isInit = true;
		sys_trans_quant_list.listSize = sysTransListSize;
		sys_trans_quant_list.transList = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jsysTransList, NULL);
		sys_trans_quant_list.quantSets = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jsysQuantSets, NULL);

		env_trans_quant_list.isInit = true;
		env_trans_quant_list.listSize = envTransListSize;
		env_trans_quant_list.transList = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jenvTransList, NULL);
		env_trans_quant_list.quantSets = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jenvQuantSets, NULL);

		if (sys_trans_quant_list.transList == NULL || sys_trans_quant_list.quantSets == NULL ||
			env_trans_quant_list.transList == NULL || env_trans_quant_list.quantSets == NULL) {
			//printf("sys_trans_quant_list or env_trans_quant_list is NULL\n");
			fflush(stdout);
			UNLOCK
			return -1;
		}
	}


	free_gr1_mem();

	int result = gr1_game(sysJ, sysJSize, envJ, envJSize, sysIni, envIni, sysTrans, envTrans,
		sysUnprime, envUnprime, sysPrimeVars, envPrimeVars, pairs, efp, eun, fpr, sca);

	(*env)->ReleasePrimitiveArrayCritical(env, jSysJ, sysJ, JNI_ABORT);
	(*env)->ReleasePrimitiveArrayCritical(env, jEnvJ, envJ, JNI_ABORT);
	if (sys_trans_quant_list.isInit) {
		(*env)->ReleasePrimitiveArrayCritical(env, jsysTransList, sys_trans_quant_list.transList, JNI_ABORT);
		(*env)->ReleasePrimitiveArrayCritical(env, jenvTransList, env_trans_quant_list.transList, JNI_ABORT);
		(*env)->ReleasePrimitiveArrayCritical(env, jsysQuantSets, sys_trans_quant_list.quantSets, JNI_ABORT);
		(*env)->ReleasePrimitiveArrayCritical(env, jenvQuantSets, env_trans_quant_list.quantSets, JNI_ABORT);
	}
	
	fflush(stdout);
	UNLOCK
	return (jboolean)result;
}

JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_gr1GameInc0
(JNIEnv *env, jclass cl, jlongArray jSysJ, jlongArray jEnvJ,
	jlong jsysIni, jlong jenvIni, jlong jSysTrans, jlong jEnvTrans,
	jlong jsysUnprime, jlong jenvUnprime, jlong jSysPrime, jlong jEnvPrime,
	jlong jPairs, jboolean efp, jboolean eun, jboolean fpr, jboolean sca,
	jint inc_bitmap, jlong inc_start_z, jlongArray inc_z_mem, jlongArray inc_z_mem_first_itr, jlongArray inc_x_mem, 
	jint jIdx, jint inc_sizeD1, jint inc_sizeD2, jintArray inc_sizeD3)
{
	LOCK
	//_CrtSetDbgFlag(_CRTDBG_ALLOC_MEM_DF | _CRTDBG_LEAK_CHECK_DF);
	//_CrtSetReportMode(_CRT_WARN, _CRTDBG_MODE_FILE);
	//_CrtSetReportFile(_CRT_WARN, _CRTDBG_FILE_STDOUT);
	//_CrtSetReportMode(_CRT_ERROR, _CRTDBG_MODE_FILE);
	//_CrtSetReportFile(_CRT_ERROR, _CRTDBG_FILE_STDOUT);
	//_CrtSetReportMode(_CRT_ASSERT, _CRTDBG_MODE_FILE);
	//_CrtSetReportFile(_CRT_ASSERT, _CRTDBG_FILE_STDOUT);

	#ifdef _DEBUG 
		//printf("running in _DEBUG mode!!!\n"); fflush(stdout);
	#endif

	// translate gr1 game data to c types
	int sysJSize = (int)(*env)->GetArrayLength(env, jSysJ);
	int envJSize = (int)(*env)->GetArrayLength(env, jEnvJ);
	//printf("sysJSize = %d\n", sysJSize);
	//printf("envJSize = %d\n", envJSize);
	DdNode** sysJ = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jSysJ, NULL);
	if (sysJ == NULL) {
		//printf("sysJ is NULL\n");
		fflush(stdout);
		UNLOCK
		return -1;
	}

	DdNode** envJ = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jEnvJ, NULL);
	if (envJ == NULL) {
		//printf("envJ is NULL\n");
		fflush(stdout);
		UNLOCK
		return -1;
	}

	int varnum = Cudd_ReadSize(manager);
	//printf("varnum = %d\n", varnum);

	CuddPairing* pairs = (CuddPairing*)(intptr_cast_type)jPairs;

	DdNode* sysTrans = (DdNode*)(intptr_cast_type)jSysTrans;
	DdNode* envTrans = (DdNode*)(intptr_cast_type)jEnvTrans;
	DdNode* sysPrimeVars = (DdNode*)(intptr_cast_type)jSysPrime;
	DdNode* envPrimeVars = (DdNode*)(intptr_cast_type)jEnvPrime;

	DdNode* sysIni = (DdNode*)(intptr_cast_type)jsysIni;
	DdNode* envIni = (DdNode*)(intptr_cast_type)jenvIni;
	DdNode* sysUnprime = (DdNode*)(intptr_cast_type)jsysUnprime;
	DdNode* envUnprime = (DdNode*)(intptr_cast_type)jenvUnprime;

	free_gr1_mem();

	//printf("gr1 data updated\n");
	// translate gr1 game incremental data to c types
	inc_gr1_data inc_data;
	inc_data.type_bitmap = (int)inc_bitmap;

	int isIncData = !(inc_data.type_bitmap == INC_TYPE_NO_INC);

	//printf("isIncData=%d\n", isIncData);
	DdNode** xArray;
	if (isIncData)
	{
		inc_data.sizeD1 = (int)inc_sizeD1;
		inc_data.sizeD2 = (int)inc_sizeD2;
		inc_data.least_removed_justice = (int)jIdx;

		int sizeD3Size = (int)(*env)->GetArrayLength(env, inc_sizeD3);
		if (sizeD3Size != inc_data.sizeD1)
		{
			//printf("inc_sizeD3 size (%d) != inc_data.sizeD1 (%d)\n", sizeD3Size, inc_data.sizeD1);
			fflush(stdout);
			UNLOCK
			return -1;
		}

		inc_data.sizeD3 = (int*)(*env)->GetIntArrayElements(env, inc_sizeD3, NULL);
		if (inc_data.sizeD3 == NULL) {
			//printf("inc_data.sizeD3 is NULL\n");
			fflush(stdout);
			UNLOCK
			return -1;
		}

		//printf("inc data about sizaes updated\n");

		inc_data.start_z = (DdNode*)(intptr_cast_type)inc_start_z;
		inc_data.z_mem = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, inc_z_mem, NULL);
		inc_data.z_mem_first_itr = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, inc_z_mem_first_itr, NULL);

		//printf("inc data about Z updated\n");
		xArray = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, inc_x_mem, NULL);
		if (xArray == NULL) {
			//printf("xArray is NULL\n");
			fflush(stdout);
			UNLOCK
			return -1;
		}

		// TODO: TMP
		//inc_data.x_mem = NULL;
		int xArrayIdx = 0;
		inc_data.x_mem = malloc(inc_data.sizeD1 * sizeof(DdNode***));
		for (int j = 0; j < inc_data.sizeD1; j++)
		{
			inc_data.x_mem[j] = malloc(inc_data.sizeD2 * sizeof(DdNode**));
			for (int i = 0; i < inc_data.sizeD2; i++)
			{
				inc_data.x_mem[j][i] = malloc(inc_data.sizeD3[j] * sizeof(DdNode*));
				for (int cy = 0; cy < inc_data.sizeD3[j]; cy++)
				{
					inc_data.x_mem[j][i][cy] = (DdNode*)(intptr_cast_type)xArray[xArrayIdx];
					xArrayIdx++;
				}
			}
		}
		//printf("inc data about X updated\n");
	}
	
	int result = gr1_game_inc(sysJ, sysJSize, envJ, envJSize, sysIni, envIni, sysTrans, envTrans,
		sysUnprime, envUnprime, sysPrimeVars, envPrimeVars, pairs, efp, eun, fpr, sca, true, inc_data);

	(*env)->ReleasePrimitiveArrayCritical(env, jSysJ, sysJ, JNI_ABORT);
	(*env)->ReleasePrimitiveArrayCritical(env, jEnvJ, envJ, JNI_ABORT);

	if (isIncData)
	{
		(*env)->ReleasePrimitiveArrayCritical(env, inc_z_mem, inc_data.z_mem, JNI_ABORT);
		(*env)->ReleasePrimitiveArrayCritical(env, inc_z_mem_first_itr, inc_data.z_mem_first_itr, JNI_ABORT);
		(*env)->ReleaseIntArrayElements(env, inc_sizeD3, inc_data.sizeD3, JNI_ABORT);
		(*env)->ReleasePrimitiveArrayCritical(env, inc_x_mem, xArray, JNI_ABORT);
		if (inc_data.x_mem != NULL) {
			for (int i = 0; i < inc_data.sizeD1; i++)
			{
				for (int j = 0; j < inc_data.sizeD2; j++)
				{
					free(inc_data.x_mem[i][j]);
				}
				free(inc_data.x_mem[i]);
			}

			free(inc_data.x_mem);
			inc_data.x_mem = NULL;
		}
	}

	UNLOCK

	return (jboolean)result;
}

/*
* Class: net_sf_javabdd_CUDDFactory
* Rabin game related functions
*/
JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_getRabinZSize0
(JNIEnv *env, jclass cl)
{
	LOCK
	jint zSize = (jint) rabin_mem.sizeD1;

	UNLOCK
	return zSize;
}

JNIEXPORT jintArray JNICALL Java_net_sf_javabdd_CUDDFactory_getRabinXSizes0
(JNIEnv *env, jclass cl)
{
	LOCK
	int size = rabin_mem.sizeD1 * rabin_mem.xSizeD2;
	
	jint * cx_memRet = malloc(size * sizeof(jint));

	int idx = 0;
	for (int i = 0; i < rabin_mem.sizeD1; i++)
	{
		for (int j = 0; j < rabin_mem.xSizeD2; j++)
		{
			cx_memRet[idx] = (jint)rabin_mem.sizeD3[i][j];
			idx++;
		}
	}

	jintArray intJavaArray = (*env)->NewIntArray(env, size);
	(*env)->SetIntArrayRegion(env, intJavaArray, 0, size, cx_memRet);

	UNLOCK
	return intJavaArray;
}

JNIEXPORT jlongArray JNICALL Java_net_sf_javabdd_CUDDFactory_getRabinXMem0
(JNIEnv *env, jclass cl)
{
	LOCK
	int j = 0, i, cx;
	int sumD3 = 0;

	for (i = 0; i < rabin_mem.sizeD1; i++)
	{
		for (j = 0; j < rabin_mem.xSizeD2; j++)
		{
			////printf("rabin_mem.sizeD3[%d][%d]=%d\n", i, j, rabin_mem.sizeD3[i][j]);  fflush(stdout);

			sumD3 += rabin_mem.sizeD3[i][j];
		}
	}
	////printf("sumD3=%d\n", sumD3);  fflush(stdout);

	int retSize = sumD3;
	intptr_cast_type * x_memRet = malloc(retSize * sizeof(intptr_cast_type));

	int idx = 0;
	for (i = 0; i < rabin_mem.sizeD1; i++)
	{
		for (j = 0; j < rabin_mem.xSizeD2; j++)
		{
			for (cx = 0; cx < rabin_mem.sizeD3[i][j]; cx++)
			{
				x_memRet[idx] = (intptr_cast_type)rabin_mem.x_mem[i][j][cx];
				idx++;
			}
		}
	}
	//printf("retSize=%d, idx=%d\n", retSize, idx);

	jlongArray longJavaArray = (*env)->NewLongArray(env, retSize);
	(*env)->SetLongArrayRegion(env, longJavaArray, 0, retSize, x_memRet);

	free(x_memRet);
	UNLOCK
	return longJavaArray;
}

JNIEXPORT jlongArray JNICALL Java_net_sf_javabdd_CUDDFactory_getRabinZMem0
(JNIEnv *env, jclass cl)
{
	LOCK
	int zSize = rabin_mem.sizeD1;// * rabin_mem.zSizeD2;
	intptr_cast_type * z_memRet = malloc(zSize * sizeof(intptr_cast_type));

	for (int i = 0; i < rabin_mem.sizeD1; i++)
	{
		z_memRet[i] = (intptr_cast_type)rabin_mem.z_mem[i];
	}

	jlongArray longJavaArray = (*env)->NewLongArray(env, zSize);
	(*env)->SetLongArrayRegion(env, longJavaArray, 0, zSize, z_memRet);

	free(z_memRet);
	UNLOCK
	return longJavaArray;
}

JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_rabinGame0
(JNIEnv *env, jclass cl, jlongArray jSysJ, jlongArray jEnvJ,
	jlong jsysIni, jlong jenvIni, jlong jSysTrans, jlong jEnvTrans,
	jlong jsysUnprime, jlong jenvUnprime, jlong jSysPrime, jlong jEnvPrime, jlong jPairs,
	jlongArray jsysTransList, jlongArray jenvTransList, jlongArray jsysQuantSets, jlongArray jenvQuantSets,
	jboolean efp, jboolean eun, jboolean fpr, jboolean sca)
{
	LOCK
	int sysJSize = (int)(*env)->GetArrayLength(env, jSysJ);
	int envJSize = (int)(*env)->GetArrayLength(env, jEnvJ);
	//printf("sysJSize = %d\n", sysJSize);
	//printf("envJSize = %d\n", envJSize);
	DdNode** sysJ = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jSysJ, NULL);
	if (sysJ == NULL) {
		//printf("sysJ is NULL\n");
		UNLOCK
		return -1;
	}

	DdNode** envJ = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jEnvJ, NULL);
	if (envJ == NULL) {
		//printf("envJ is NULL\n");
		UNLOCK
		return -1;
	}

	int varnum = Cudd_ReadSize(manager);
	//printf("varnum = %d\n", varnum);

	CuddPairing* pairs = (CuddPairing*)(intptr_cast_type)jPairs;

	DdNode* sysTrans = (DdNode*)(intptr_cast_type)jSysTrans;
	DdNode* envTrans = (DdNode*)(intptr_cast_type)jEnvTrans;
	DdNode* sysPrimeVars = (DdNode*)(intptr_cast_type)jSysPrime;
	DdNode* envPrimeVars = (DdNode*)(intptr_cast_type)jEnvPrime;

	DdNode* sysIni = (DdNode*)(intptr_cast_type)jsysIni;
	DdNode* envIni = (DdNode*)(intptr_cast_type)jenvIni;
	DdNode* sysUnprime = (DdNode*)(intptr_cast_type)jsysUnprime;
	DdNode* envUnprime = (DdNode*)(intptr_cast_type)jenvUnprime;

	int sysTransListSize = (int)(*env)->GetArrayLength(env, jsysTransList);
	int envTransListSize = (int)(*env)->GetArrayLength(env, jenvTransList);
	int sysQuantSetsSize = (int)(*env)->GetArrayLength(env, jsysQuantSets);
	int envQuantSetsSize = (int)(*env)->GetArrayLength(env, jenvQuantSets);
	//printf("sysTransListSize = %d\n", sysTransListSize);
	//printf("envTransListSize = %d\n", envTransListSize);
	//printf("sysQuantSetsSize = %d\n", sysQuantSetsSize);
	//printf("envQuantSetsSize = %d\n", envQuantSetsSize);

	if (sysTransListSize != sysQuantSetsSize || envTransListSize != envQuantSetsSize) {
		//printf("TransListSize != QuantSetsSize (for sys or env)\n");
		fflush(stdout);
		UNLOCK
		return -1;
	}

	if (sca) {
		//printf("simultaneous conjuction and abstraction: use Cudd_bddAndAbstract\n");
	}
	if (sysTransListSize == 0 || envTransListSize == 0) {
		//printf("not given trans-quantsets lists, will use original control\n");
		sys_trans_quant_list.isInit = false;
		env_trans_quant_list.isInit = false;
	}
	else {
		//printf("given trans-quantsets lists, will use the decomposition control\n");
		sys_trans_quant_list.isInit = true;
		sys_trans_quant_list.listSize = sysTransListSize;
		sys_trans_quant_list.transList = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jsysTransList, NULL);
		sys_trans_quant_list.quantSets = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jsysQuantSets, NULL);

		env_trans_quant_list.isInit = true;
		env_trans_quant_list.listSize = envTransListSize;
		env_trans_quant_list.transList = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jenvTransList, NULL);
		env_trans_quant_list.quantSets = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jenvQuantSets, NULL);

		if (sys_trans_quant_list.transList == NULL || sys_trans_quant_list.quantSets == NULL ||
			env_trans_quant_list.transList == NULL || env_trans_quant_list.quantSets == NULL) {
			//printf("sys_trans_quant_list or env_trans_quant_list is NULL\n");
			fflush(stdout);
			UNLOCK
			return -1;
		}
	}

	free_rabin_mem();

	int result = rabin_game(sysJ, sysJSize, envJ, envJSize, sysIni, envIni, sysTrans, envTrans,
		sysUnprime, envUnprime, sysPrimeVars, envPrimeVars, pairs, efp, eun, fpr, sca);

	(*env)->ReleasePrimitiveArrayCritical(env, jSysJ, sysJ, JNI_ABORT);
	(*env)->ReleasePrimitiveArrayCritical(env, jEnvJ, envJ, JNI_ABORT);
	if (sys_trans_quant_list.isInit) {
		(*env)->ReleasePrimitiveArrayCritical(env, jsysTransList, sys_trans_quant_list.transList, JNI_ABORT);
		(*env)->ReleasePrimitiveArrayCritical(env, jenvTransList, env_trans_quant_list.transList, JNI_ABORT);
		(*env)->ReleasePrimitiveArrayCritical(env, jsysQuantSets, sys_trans_quant_list.quantSets, JNI_ABORT);
		(*env)->ReleasePrimitiveArrayCritical(env, jenvQuantSets, env_trans_quant_list.quantSets, JNI_ABORT);
	}
    fflush(stdout);
	UNLOCK

	return (jboolean)result;
}

JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_rabinGameInc0
(JNIEnv *env, jclass cl, jlongArray jSysJ, jlongArray jEnvJ,
	jlong jsysIni, jlong jenvIni, jlong jSysTrans, jlong jEnvTrans,
	jlong jsysUnprime, jlong jenvUnprime, jlong jSysPrime, jlong jEnvPrime,
	jlong jPairs, jboolean efp, jboolean eun, jboolean fpr, jboolean sca,
	jint inc_bitmap, jlong inc_start_z, jlongArray inc_z_mem, jlongArray inc_x_mem,
	jint jIdx, jint inc_sizeD1, jint inc_sizeD2, jintArray inc_sizeD3)
{
	LOCK
	int sysJSize = (int)(*env)->GetArrayLength(env, jSysJ);
	int envJSize = (int)(*env)->GetArrayLength(env, jEnvJ);
	//printf("sysJSize = %d\n", sysJSize);
	//printf("envJSize = %d\n", envJSize);
	DdNode** sysJ = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jSysJ, NULL);
	if (sysJ == NULL) {
		//printf("sysJ is NULL\n");
		UNLOCK
		return -1;
	}

	DdNode** envJ = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, jEnvJ, NULL);
	if (envJ == NULL) {
		//printf("envJ is NULL\n");
		UNLOCK
		return -1;
	}

	int varnum = Cudd_ReadSize(manager);
	//printf("varnum = %d\n", varnum);

	CuddPairing* pairs = (CuddPairing*)(intptr_cast_type)jPairs;

	DdNode* sysTrans = (DdNode*)(intptr_cast_type)jSysTrans;
	DdNode* envTrans = (DdNode*)(intptr_cast_type)jEnvTrans;
	DdNode* sysPrimeVars = (DdNode*)(intptr_cast_type)jSysPrime;
	DdNode* envPrimeVars = (DdNode*)(intptr_cast_type)jEnvPrime;

	DdNode* sysIni = (DdNode*)(intptr_cast_type)jsysIni;
	DdNode* envIni = (DdNode*)(intptr_cast_type)jenvIni;
	DdNode* sysUnprime = (DdNode*)(intptr_cast_type)jsysUnprime;
	DdNode* envUnprime = (DdNode*)(intptr_cast_type)jenvUnprime;

	free_rabin_mem();

	//printf("rabin data updated\n");
	// translate gr1 game incremental data to c types
	inc_rabin_data inc_data;
	inc_data.type_bitmap = (int)inc_bitmap;

	int isIncData = !(inc_data.type_bitmap == INC_TYPE_NO_INC);

	//printf("isIncData=%d\n", isIncData);

	DdNode** xArray;
	int * sizeD3;
	if (isIncData)
	{
		inc_data.sizeD1 = (int)inc_sizeD1;
		inc_data.sizeD2 = (int)inc_sizeD2;
		inc_data.least_removed_justice = (int)jIdx;

		int sizeD3Size = (int)(*env)->GetArrayLength(env, inc_sizeD3);
		if (sizeD3Size != (inc_data.sizeD1 * inc_data.sizeD2))
		{
			//printf("inc_sizeD3 size (%d) != inc_data.sizeD1 (%d)\n", sizeD3Size, inc_data.sizeD1);
			fflush(stdout);
			UNLOCK
			return -1;
		}

		sizeD3 = (int*)(*env)->GetIntArrayElements(env, inc_sizeD3, NULL);
		if (sizeD3 == NULL) {
			//printf("inc_data.sizeD3 is NULL\n");
			fflush(stdout);
			UNLOCK
			return -1;
		}

		int cx = 0;
		inc_data.sizeD3 = malloc(inc_data.sizeD1 * sizeof(int*));
		for (int i = 0; i < inc_data.sizeD1; i++)
		{
			inc_data.sizeD3[i] = malloc(inc_data.sizeD2 * sizeof(int));
			for (int k = 0; k < inc_data.sizeD2; k++)
			{
				inc_data.sizeD3[i][k] = sizeD3[cx];
				////printf("inc_data.sizeD3[%d][%d] = %d\n", i, k, inc_data.sizeD3[i][k]); fflush(stdout);
				cx++;
			}
		}
		//printf("cx = %d\n", cx);
		//printf("inc data of sizes updated\n");

		inc_data.start_z = (DdNode*)(intptr_cast_type)inc_start_z;
		inc_data.z_mem = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, inc_z_mem, NULL);

		//printf("inc data about Z updated\n");

		xArray = (DdNode**)(intptr_cast_type*)(*env)->GetPrimitiveArrayCritical(env, inc_x_mem, NULL);
		if (xArray == NULL) {
			//printf("xArray is NULL\n");
			fflush(stdout);
			UNLOCK
			return -1;
		}

		int xArrayIdx = 0;
		inc_data.x_mem = malloc(inc_data.sizeD1 * sizeof(DdNode***));
		for (int j = 0; j < inc_data.sizeD1; j++)
		{
			inc_data.x_mem[j] = malloc(inc_data.sizeD2 * sizeof(DdNode**));
			for (int i = 0; i < inc_data.sizeD2; i++)
			{
				inc_data.x_mem[j][i] = malloc(inc_data.sizeD3[j][i] * sizeof(DdNode*));
				for (int cy = 0; cy < inc_data.sizeD3[j][i]; cy++)
				{
					inc_data.x_mem[j][i][cy] = (DdNode*)(intptr_cast_type)xArray[xArrayIdx];
					xArrayIdx++;
				}
			}
		}
		//printf("xArrayIdx = %d\n", xArrayIdx);
		//printf("inc data about X updated\n");
	}

	int result = rabin_game_inc(sysJ, sysJSize, envJ, envJSize, sysIni, envIni, sysTrans, envTrans,
		sysUnprime, envUnprime, sysPrimeVars, envPrimeVars, pairs, efp, eun, fpr, sca, true, inc_data);

	(*env)->ReleasePrimitiveArrayCritical(env, jSysJ, sysJ, JNI_ABORT);
	(*env)->ReleasePrimitiveArrayCritical(env, jEnvJ, envJ, JNI_ABORT);

	if (isIncData)
	{
		(*env)->ReleasePrimitiveArrayCritical(env, inc_z_mem, inc_data.z_mem, JNI_ABORT);
		(*env)->ReleaseIntArrayElements(env, inc_sizeD3, sizeD3, JNI_ABORT);
		(*env)->ReleasePrimitiveArrayCritical(env, inc_x_mem, xArray, JNI_ABORT);
		if (inc_data.x_mem != NULL) {
			for (int i = 0; i < inc_data.sizeD1; i++)
			{
				for (int j = 0; j < inc_data.sizeD2; j++)
				{
					free(inc_data.x_mem[i][j]);
				}
				free(inc_data.x_mem[i]);
				free(inc_data.sizeD3[i]);
			}

			free(inc_data.x_mem);
			inc_data.x_mem = NULL;
			free(inc_data.sizeD3);
			inc_data.sizeD3 = NULL;
		}
	}
	UNLOCK

	return (jboolean)result;
}
