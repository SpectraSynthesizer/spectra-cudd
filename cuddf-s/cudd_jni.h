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

/* DO NOT EDIT THIS FILE - it is machine generated */
#include <jni.h>
/* Header for class net_sf_javabdd_CUDDFactory */

#ifndef _Included_net_sf_javabdd_CUDDFactory
#define _Included_net_sf_javabdd_CUDDFactory
#ifdef __cplusplus
extern "C" {
#endif
	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    registerNatives
	* Signature: ()V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_registerNatives
		(JNIEnv *, jclass);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    initialize0
	* Signature: (II)V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_initialize0
		(JNIEnv *, jclass, jint, jint);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    isInitialized0
	* Signature: ()Z
	*/
	JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_isInitialized0
		(JNIEnv *, jclass);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    done0
	* Signature: ()V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_done0
		(JNIEnv *, jclass);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    varNum0
	* Signature: ()I
	*/
	JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_varNum0
		(JNIEnv *, jclass);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    setVarNum0
	* Signature: (IZ)I
	*/
	JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_setVarNum0
		(JNIEnv *, jclass, jint, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    ithVar0
	* Signature: (IZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_ithVar0
		(JNIEnv *, jclass, jint, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    level2Var0
	* Signature: (I)I
	*/
	JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_level2Var0
		(JNIEnv *, jclass, jint);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    var2Level0
	* Signature: (I)I
	*/
	JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_var2Level0
		(JNIEnv *, jclass, jint);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    setVarOrder0
	* Signature: ([I)V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_setVarOrder0
		(JNIEnv *, jclass, jintArray);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    getAllocNum0
	* Signature: ()I
	*/
	JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_getAllocNum0
		(JNIEnv *, jclass);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    getNodeNum0
	* Signature: ()I
	*/
	JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_getNodeNum0
		(JNIEnv *, jclass);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    getCacheSize0
	* Signature: ()I
	*/
	JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_getCacheSize0
		(JNIEnv *, jclass);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    var0
	* Signature: (J)I
	*/
	JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_var0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    high0
	* Signature: (JZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_high0
		(JNIEnv *, jclass, jlong, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    low0
	* Signature: (JZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_low0
		(JNIEnv *, jclass, jlong, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    not0
	* Signature: (JZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_not0
		(JNIEnv *, jclass, jlong, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    ite0
	* Signature: (JJJZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_ite0
		(JNIEnv *, jclass, jlong, jlong, jlong, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    relprod0
	* Signature: (JJJ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_relprod0
		(JNIEnv *, jclass, jlong, jlong, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    compose0
	* Signature: (JJIZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_compose0
		(JNIEnv *, jclass, jlong, jlong, jint, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    exist0
	* Signature: (JJZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_exist0
		(JNIEnv *, jclass, jlong, jlong, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    forAll0
	* Signature: (JJZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_forAll0
		(JNIEnv *, jclass, jlong, jlong, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    simplify0
	* Signature: (JJZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_simplify0
		(JNIEnv *, jclass, jlong, jlong, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    restrict0
	* Signature: (JJZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_restrict0
		(JNIEnv *, jclass, jlong, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    restrictWith0
	* Signature: (JJZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_restrictWith0
		(JNIEnv *env, jclass cl, jlong a, jlong b, jboolean derefOther);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    support0
	* Signature: (JZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_support0
		(JNIEnv *, jclass, jlong, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    apply0
	* Signature: (JJIZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_apply0
		(JNIEnv *, jclass, jlong, jlong, jint, jboolean, jboolean, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    satOne0
	* Signature: (JZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_satOne0
		(JNIEnv *, jclass, jlong, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    nodeCount0
	* Signature: (J)I
	*/
	JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_nodeCount0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    pathCount0
	* Signature: (J)D
	*/
	JNIEXPORT jdouble JNICALL Java_net_sf_javabdd_CUDDFactory_pathCount0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    satCount0
	* Signature: (J)D
	*/
	JNIEXPORT jdouble JNICALL Java_net_sf_javabdd_CUDDFactory_satCount0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    addRef
	* Signature: (J)V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_addRef
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    delRef
	* Signature: (JZ)V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_delRef
		(JNIEnv *, jclass, jlong, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    veccompose0
	* Signature: (JJZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_veccompose0
		(JNIEnv *, jclass, jlong, jlong, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    replace0
	* Signature: (JJZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_replace0
		(JNIEnv *, jclass, jlong, jlong, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    alloc
	* Signature: (Z)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_alloc
		(JNIEnv *, jclass, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    set0
	* Signature: (JIIZ)V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_set0
		(JNIEnv *, jclass, jlong, jint, jint, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    set2
	* Signature: (JIJ)V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_set2
		(JNIEnv *, jclass, jlong, jint, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    reset0
	* Signature: (JZ)V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_reset0
		(JNIEnv *, jclass, jlong, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    free0
	* Signature: (J)V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_free0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    isZeroOneADD0
	* Signature: (J)Z
	*/
	JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_isZeroOneADD0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    addConst0
	* Signature: (D)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addConst0
		(JNIEnv *, jclass, jdouble);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    isAddConst0
	* Signature: (J)Z
	*/
	JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_isAddConst0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    addFindMax0
	* Signature: (J)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addFindMax0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    addFindMin0
	* Signature: (J)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addFindMin0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    retrieveConstValue0
	* Signature: (J)D
	*/
	JNIEXPORT jdouble JNICALL Java_net_sf_javabdd_CUDDFactory_retrieveConstValue0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    addAdditiveNeg0
	* Signature: (J)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addAdditiveNeg0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    addApplyLog0
	* Signature: (J)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addApplyLog0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    reorder0
	* Signature: (Lnet/sf/javabdd/BDDFactory/ReorderMethod;ZI)V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_reorder0
		(JNIEnv*, jclass, jobject);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    autoReorder0
	* Signature: (Lnet/sf/javabdd/BDDFactory/ReorderMethod;)V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_autoReorder0
		(JNIEnv*, jclass, jobject, jboolean, jint);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    getreordermethod0
	* Signature: ()Lnet/sf/javabdd/BDDFactory/ReorderMethod;
	*/
	JNIEXPORT jobject JNICALL Java_net_sf_javabdd_CUDDFactory_getreordermethod0
		(JNIEnv *, jclass);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    autoReorder1
	* Signature: ()V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_autoReorder1
		(JNIEnv *, jclass);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    reorderVerbose0
	* Signature: (I)I
	*/
	JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_reorderVerbose0
		(JNIEnv *, jclass, jint);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    addVarBlock0
	* Signature: (IIZ)V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_addVarBlock0
		(JNIEnv *, jclass, jint, jint, jboolean);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    clearVarBlocks0
	* Signature: ()V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_clearVarBlocks0
		(JNIEnv *, jclass);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    printStat0
	* Signature: ()V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_printStat0
		(JNIEnv *, jclass);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    toADD0
	* Signature: (J)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_toADD0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    toBDD0
	* Signature: (J)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_toBDD0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    toBDDThreshold
	* Signature: (JD)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_toBDDThreshold
		(JNIEnv *, jclass, jlong, jdouble);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    toBDDStrictThreshold
	* Signature: (JD)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_toBDDStrictThreshold
		(JNIEnv *, jclass, jlong, jdouble);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    toBDDInterval
	* Signature: (JDD)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_toBDDInterval
		(JNIEnv *, jclass, jlong, jdouble, jdouble);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    toBDDIthBit
	* Signature: (JI)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_toBDDIthBit
		(JNIEnv *, jclass, jlong, jint);

	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    varSupportIndex0
	* Signature: (J)[I
	*/
	JNIEXPORT jintArray JNICALL Java_net_sf_javabdd_CUDDFactory_varSupportIndex0
		(JNIEnv *, jclass, jlong);

	/*
	* Class:   net_sf_javabdd_CUDDFactory
	* Method : varSupportIndex0
	* Signature : (JI)V
	*/
	JNIEXPORT void JNICALL Java_net_sf_javabdd_CUDDFactory_printSet0
		(JNIEnv *, jclass, jlong, jint);
	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:   arithmeticZero0
	* Signature: ()J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_arithmeticZero0
		(JNIEnv *env, jclass cl);
	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    logicZero0
	* Signature: ()J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_logicZero0
		(JNIEnv *env, jclass cl);
	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    replaceWith0
	* Signature: (JJZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_replaceWith0
		(JNIEnv *env, jclass cl, jlong a, jlong b, jboolean is_add);
	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    addAbstractMin0
	* Signature: (JJZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addAbstractMin0
		(JNIEnv *env, jclass cl, jlong a, jlong b);
	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    addAbstractMax0
	* Signature: (JJZ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_addAbstractMax0
		(JNIEnv *env, jclass cl, jlong a, jlong b);
	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:  arithmeticMinusInfinity0
	* Signature: ()J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_arithmeticMinusInfinity0
		(JNIEnv *env, jclass cl);
	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:  arithmeticPlusInfinity0
	* Signature: ()J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_arithmeticPlusInfinity0
		(JNIEnv *env, jclass cl);
	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    determinizeController0
	* Signature: (JJ)J
	*/
	JNIEXPORT jlong JNICALL Java_net_sf_javabdd_CUDDFactory_determinizeController0
		(JNIEnv *env, jclass cl, jlong a, jlong b, jboolean is_add);
	/*
	* Class:     net_sf_javabdd_CUDDFactory
	* Method:    negCycleCheck0
	* Signature: (JJJJ)Z
	*/
	JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_negCycleCheck0
		(JNIEnv *env, jclass cl, jlong a, jlong s, jlong v, jlong p);

	/*
	* Class: net_sf_javabdd_CUDDFactory
	* GR1 game related functions
	*/
	JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_equalBDDs0
		(JNIEnv *, jclass, jlong, jlong);
	JNIEXPORT jintArray JNICALL Java_net_sf_javabdd_CUDDFactory_getAttrSizes0
		(JNIEnv *, jclass);
	JNIEXPORT jlongArray JNICALL Java_net_sf_javabdd_CUDDFactory_getXMem0
		(JNIEnv *, jclass);
	JNIEXPORT jlongArray JNICALL Java_net_sf_javabdd_CUDDFactory_getYMem0
		(JNIEnv *, jclass);
	JNIEXPORT jlongArray JNICALL Java_net_sf_javabdd_CUDDFactory_getZMem0
		(JNIEnv *, jclass);
	JNIEXPORT jlongArray JNICALL Java_net_sf_javabdd_CUDDFactory_getZMemFirstItr0
		(JNIEnv *, jclass);
	JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_gr1Game0
		(JNIEnv *, jclass, jlongArray, jlongArray, jlong, jlong, jlong, jlong,
			jlong, jlong, jlong, jlong, jlong, jlongArray, jlongArray, jlongArray, jlongArray, 
			jboolean, jboolean, jboolean, jboolean);
	JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_gr1GameInc0
		(JNIEnv *, jclass, jlongArray, jlongArray, jlong, jlong, jlong, jlong,
			jlong, jlong, jlong, jlong,	jlong, jboolean, jboolean, jboolean, jboolean,
			jint, jlong, jlongArray, jlongArray, jlongArray, jint, jint, jint, jintArray);
	JNIEXPORT jlongArray JNICALL Java_net_sf_javabdd_CUDDFactory_getRabinXMem0
		(JNIEnv *env, jclass cl);
	JNIEXPORT jlongArray JNICALL Java_net_sf_javabdd_CUDDFactory_getRabinZMem0
		(JNIEnv *, jclass);
	JNIEXPORT jint JNICALL Java_net_sf_javabdd_CUDDFactory_getRabinZSize0
		(JNIEnv *, jclass);
	JNIEXPORT jintArray JNICALL Java_net_sf_javabdd_CUDDFactory_getRabinXSizes0
		(JNIEnv *, jclass);
	JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_rabinGame0
		(JNIEnv *, jclass, jlongArray, jlongArray, jlong, jlong, jlong, jlong,
			jlong, jlong, jlong, jlong, jlong, jlongArray, jlongArray, jlongArray, jlongArray,
			jboolean, jboolean, jboolean, jboolean);
	JNIEXPORT jboolean JNICALL Java_net_sf_javabdd_CUDDFactory_rabinGameInc0
		(JNIEnv *, jclass, jlongArray, jlongArray, jlong, jlong, jlong, jlong,
		jlong, jlong, jlong, jlong, jlong, jboolean, jboolean, jboolean, jboolean,
		jint, jlong, jlongArray, jlongArray, jint, jint, jint, jintArray);

#ifdef __cplusplus
}
#endif
#endif
/* Header for class net_sf_javabdd_CUDDFactory_CUDDADDBitVector */

#ifndef _Included_net_sf_javabdd_CUDDFactory_CUDDADDBitVector
#define _Included_net_sf_javabdd_CUDDFactory_CUDDADDBitVector
#ifdef __cplusplus
extern "C" {
#endif
#ifdef __cplusplus
}
#endif
#endif
/* Header for class net_sf_javabdd_CUDDFactory_CUDDBDDBitVector */

#ifndef _Included_net_sf_javabdd_CUDDFactory_CUDDBDDBitVector
#define _Included_net_sf_javabdd_CUDDFactory_CUDDBDDBitVector
#ifdef __cplusplus
extern "C" {
#endif
#ifdef __cplusplus
}
#endif
#endif
/* Header for class net_sf_javabdd_CUDDFactory_CUDDADDPairing */

#ifndef _Included_net_sf_javabdd_CUDDFactory_CUDDADDPairing
#define _Included_net_sf_javabdd_CUDDFactory_CUDDADDPairing
#ifdef __cplusplus
extern "C" {
#endif
#ifdef __cplusplus
}
#endif
#endif
/* Header for class net_sf_javabdd_CUDDFactory_CUDDBDDPairing */

#ifndef _Included_net_sf_javabdd_CUDDFactory_CUDDBDDPairing
#define _Included_net_sf_javabdd_CUDDFactory_CUDDBDDPairing
#ifdef __cplusplus
extern "C" {
#endif
#ifdef __cplusplus
}
#endif
#endif
/* Header for class net_sf_javabdd_CUDDFactory_CUDDADDDomain */

#ifndef _Included_net_sf_javabdd_CUDDFactory_CUDDADDDomain
#define _Included_net_sf_javabdd_CUDDFactory_CUDDADDDomain
#ifdef __cplusplus
extern "C" {
#endif
#ifdef __cplusplus
}
#endif
#endif
/* Header for class net_sf_javabdd_CUDDFactory_CUDDBDDDomain */

#ifndef _Included_net_sf_javabdd_CUDDFactory_CUDDBDDDomain
#define _Included_net_sf_javabdd_CUDDFactory_CUDDBDDDomain
#ifdef __cplusplus
extern "C" {
#endif
#ifdef __cplusplus
}
#endif
#endif
/* Header for class net_sf_javabdd_CUDDFactory_CUDDADD */

#ifndef _Included_net_sf_javabdd_CUDDFactory_CUDDADD
#define _Included_net_sf_javabdd_CUDDFactory_CUDDADD
#ifdef __cplusplus
extern "C" {
#endif
#ifdef __cplusplus
}
#endif
#endif
/* Header for class net_sf_javabdd_CUDDFactory_CUDDBDD */

#ifndef _Included_net_sf_javabdd_CUDDFactory_CUDDBDD
#define _Included_net_sf_javabdd_CUDDFactory_CUDDBDD
#ifdef __cplusplus
extern "C" {
#endif
#ifdef __cplusplus
}
#endif
#endif
/* Header for class net_sf_javabdd_CUDDFactory_CUDDADDFactory */

#ifndef _Included_net_sf_javabdd_CUDDFactory_CUDDADDFactory
#define _Included_net_sf_javabdd_CUDDFactory_CUDDADDFactory
#ifdef __cplusplus
extern "C" {
#endif
#ifdef __cplusplus
}
#endif
#endif
