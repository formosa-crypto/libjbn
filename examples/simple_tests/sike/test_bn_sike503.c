#include <stdio.h>
#include <stdint.h>
#include <assert.h>

#include "libjbn_fp.h"

#define NLIMBS 8

uint64_t t[NLIMBS] =
 { 0xfffffffffffffff0,
   0xffffffffffffffff,
   0xffffffffffffffff,
   0xabffffffffffffff,
   0x13085bda2211e7a0,
   0x1b9bf6c87b7e7daf,
   0x6045c6bdda77a4d0,
   0x004066f541811e1e };


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
    bn_print("Expecting", x);
    bn_print("Got", y);
  } else {
    printf("...OK!\n");
  }
  return r;
}

int main() {
  uint64_t x[NLIMBS], y[NLIMBS];
  bn_copy(x, t);
  fp_toM(x, x);
  bn_copy(y, x);
  fp_inv(x, x);
  fp_mul(x, x, y);
  fp_mul(x, x, y);
  fp_fromM(x, x);
  bn_check("invm & mulm", t, x);
}
