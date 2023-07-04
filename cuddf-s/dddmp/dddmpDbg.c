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

/**CFile**********************************************************************

  FileName     [dddmpDbg.c]

  PackageName  [dddmp]

  Synopsis     [Functions to display BDD files]

  Description  [Functions to display BDD files in binary format
    ]

  Author       [Gianpiero Cabodi and Stefano Quer]

  Copyright   [
    Copyright (c) 2004 by Politecnico di Torino.
    All Rights Reserved. This software is for educational purposes only.
    Permission is given to academic institutions to use, copy, and modify
    this software and its documentation provided that this introductory
    message is not removed, that this software and its documentation is
    used for the institutions' internal research and educational purposes,
    and that no monies are exchanged. No guarantee is expressed or implied
    by the distribution of this code.
    Send bug-reports and/or questions to:
    {gianpiero.cabodi,stefano.quer}@polito.it.
    ]

******************************************************************************/

#include "dddmpInt.h"

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


/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/


/**AutomaticEnd***************************************************************/


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis     [Display a binary dump file in a text file]

  Description  [Display a binary dump file in a text file]

  SideEffects  [None]

  SeeAlso      [Dddmp_cuddBddStore , Dddmp_cuddBddLoad ]

******************************************************************************/

int
Dddmp_cuddBddDisplayBinary(
  char *fileIn  /* IN: name of binary file */,
  char *fileOut /* IN: name of text file */
  )
{
  FILE *fp, *fpo; 
  int id, size;
  struct binary_dd_code code;
  char buf[1000];
  int nnodes, i;
  char *retval;

  fp = fopen (fileIn, "rb");
  if (fp == 0) {
    return (0);
  }

  fpo = fopen (fileOut, "w");
  if (fpo == 0) {
    return (0);
  }

  while (fgets(buf, 999,fp)!=NULL) {
    fprintf (fpo, "%s", buf);
    if (strncmp(buf, ".nnodes", 7) == 0) {
      sscanf (buf, "%*s %d", &nnodes);
    }
    if (strncmp(buf, ".rootids", 8) == 0) {
      break;
    }
  }

  for (i=1; i<=nnodes; i++) {
    if (feof(fp)) {
      return (0);
    }
    if (DddmpReadCode(fp,&code) == 0) {
      return (0);                        
    }
    fprintf (fpo, "c  : v %d | T %d | E %d\n",
      (int)code.V, (int)code.T, 
      (code.Ecompl ? -(int)(code.E) : (int)(code.E)));
    if (code.V == DDDMP_TERMINAL) {
      continue;
    }
    if (code.V <= DDDMP_RELATIVE_ID) {
      size = DddmpReadInt(fp,&id);
      if (size == 0) {
        return (0);
      }
      fprintf(fpo, "v(%d): %d\n", size, id);
    }
    if (code.T <= DDDMP_RELATIVE_ID) {
      size = DddmpReadInt(fp,&id);
      if (size == 0) {
        return (0);
      }
      fprintf(fpo, "T(%d): %d\n", size, id);
    }
    if (code.E <= DDDMP_RELATIVE_ID) {
      size = DddmpReadInt(fp,&id);
      if (size == 0) {
        return (0);
      }
      fprintf(fpo, "E(%d): %d\n", size, id);
    }

  }

  retval = fgets(buf, 999,fp);
  if (!retval || strncmp(buf, ".end", 4) != 0) {
    return (0);
  }

  fprintf(fpo, ".end");

  fclose(fp);
  fclose(fpo);

  return (1);
}


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/


