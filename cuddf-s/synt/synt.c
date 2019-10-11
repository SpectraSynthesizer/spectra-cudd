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

sizeD1 = 0;
sizeD2 = 0;

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