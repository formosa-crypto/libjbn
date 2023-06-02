#include <stdio.h>
#include <stdint.h>
#include <assert.h>

#include "libjbn_fp.h"

#define NLIMBS 12

uint64_t p751[NLIMBS] =
 { 0xffffffffffffffff,
   0xffffffffffffffff,
   0xffffffffffffffff,
   0xffffffffffffffff,
   0xffffffffffffffff,
   0xeeafffffffffffff,
   0xe3ec968549f878a8,
   0xda959b1a13f7cc76,
   0x084e9867d6ebe876,
   0x8562b5045cb25748,
   0x0e12909f97badc66,
   0x00006fe5d541f71c };

uint64_t one[NLIMBS] =
 { 0x0000000000000001,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000 };

uint64_t t1[NLIMBS] =
 { 0xfffffffffffffff0,
   0xffffffffffffffff,
   0xffffffffffffffff,
   0xffffffffffffffff,
   0xffffffffffffffff,
   0xeeafffffffffffff,
   0xe3ec968549f878a8,
   0xda959b1a13f7cc76,
   0x084e9867d6ebe876,
   0x8562b5045cb25748,
   0x0e12909f97badc66,
   0x00006fe5d541f71c };

uint64_t t2[NLIMBS] =
 { 0xffffffffffffffff,
   0xffffffffffffffff,
   0xffffffffffffffff,
   0xffffffffffffffff,
   0xffffffffffffffff,
   0xeeafffffffffffff,
   0xe3ec968549f878a8,
   0xda959b1a13f7cc76,
   0x084e9867d6ebe876,
   0x8562b5045cb25748,
   0x0e12909f97badc66,
   0x00006fe5d541f710 };

uint64_t add12[NLIMBS] =
 { 0xfffffffffffffff0,
   0xffffffffffffffff,
   0xffffffffffffffff,
   0xffffffffffffffff, 
   0xffffffffffffffff, 
   0xeeafffffffffffff, 
   0xe3ec968549f878a8, 
   0xda959b1a13f7cc76, 
   0x084e9867d6ebe876, 
   0x8562b5045cb25748, 
   0x0e12909f97badc66, 
   0x00006fe5d541f710 };

uint64_t sub12[NLIMBS] = 
 { 0xfffffffffffffff1, 
   0xffffffffffffffff, 
   0xffffffffffffffff, 
   0xffffffffffffffff, 
   0xffffffffffffffff, 
   0xffffffffffffffff, 
   0xffffffffffffffff, 
   0xffffffffffffffff, 
   0xffffffffffffffff, 
   0xffffffffffffffff, 
   0xffffffffffffffff, 
   0x000000000000000b };

uint64_t sub21[NLIMBS] = 
 { 0x000000000000000e, 
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0xeeb0000000000000,
   0xe3ec968549f878a8,
   0xda959b1a13f7cc76,
   0x084e9867d6ebe876,
   0x8562b5045cb25748,
   0x0e12909f97badc66,
   0x00006fe5d541f710 };

uint64_t mul12[NLIMBS] =
 { 0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x0000000000000000,
   0x00000000000000b4 };

uint64_t inv1[NLIMBS] = 
 { 0xcccccccccccccccc,
   0xcccccccccccccccc,
   0xcccccccccccccccc,
   0xcccccccccccccccc,
   0xcccccccccccccccc,
   0xe23ccccccccccccc,
   0x2fad7f72cfd8587b,
   0x17c30b5763f9fc57,
   0x7d8ef84c26247746,
   0x2e9db7f221d81ddf,
   0xe82fbf63f7cd4c4b,
   0x0000520ef1b8e869 };


void bn_print(char* str, uint64_t x[]) {
 int i;
 if (str!=NULL) printf("%s = [ ", str);
 for (i=0; i<NLIMBS; i++) {
   if (0 < i) printf(", ");
   printf("0x%016llx ", x[i]);
 }
 printf("]\n");
}

void bn2_print(char* str, uint64_t x[]) {
 int i;
 if (str!=NULL) printf("%s = [ ", str);
 for (i=0; i<2*NLIMBS; i++) {
   if (0 < i) printf(", ");
   printf("0x%016llx ", x[i]);
 }
 printf("]\n");
}

int bn_check(char* str, uint64_t x[], uint64_t y[]) {
  int r = bn_eq(x,y);
  printf("TESTING %s: \n", str);
  if (! r ) {
    printf("Expecting: ");
    bn_print("", x);
    printf(", but got: ");
    bn_print("", y);
  } else {
    printf("...OK!\n");
  }
  return r;
}

int main() {
  uint64_t x[NLIMBS], y[NLIMBS];
  fp_add(x, t1, t2);
  bn_check("addm", add12, x);
  fp_sub(x, t1, t2);
  bn_check("subm", sub12, x);
  fp_sub(x, t2, t1);
  bn_check("subm", sub21, x);
  bn_copy(x, t1);
  fp_toM(x, x);
  bn_copy(y, t2);
  fp_toM(y, y);
  fp_mul(x, x, y);
  fp_fromM(x, x);
  bn_check("mulm", mul12, x);
  bn_copy(x, t1);
  fp_toM(x, x);
  fp_inv(x, x);
  fp_fromM(x, x);
  bn_check("invm", inv1, x);
  bn_copy(x, t1);
  fp_toM(x, x);
  fp_inv(x, x);
  bn_copy(y, t1);
  fp_toM(y, y);
  fp_mul(x, x, y);
  fp_mul(x, x, y);
  fp_fromM(x, x);
  bn_check("invm & mulm", t1, x);
}
