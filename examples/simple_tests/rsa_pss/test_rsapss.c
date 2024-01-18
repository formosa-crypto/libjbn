#include <stdio.h>
#include <stdint.h>
#include <assert.h>

#include "libjbn_fp.h"

#define NLIMBS 16

uint64_t t[NLIMBS] =
 { 0x0000000000000001,
   0x0000000000000002,
   0x0000000000000003,
   0x0000000000000004,
   0x0000000000000005,
   0x0000000000000006,
   0x0000000000000007,
   0x0000000000000008,
   0x0000000000000009,
   0x000000000000000A,
   0x000000000000000B,
   0x000000000000000C,
   0x000000000000000D,
   0x000000000000000E,
   0x000000000000000F,
   0x0000000000000000 };

uint64_t e[NLIMBS] =
 { 0x0000000000010001
 , 0x0000000000000000
 , 0x0000000000000000
 , 0x0000000000000000
 , 0x0000000000000000
 , 0x0000000000000000
 , 0x0000000000000000
 , 0x0000000000000000
 , 0x0000000000000000
 , 0x0000000000000000
 , 0x0000000000000000
 , 0x0000000000000000
 , 0x0000000000000000
 , 0x0000000000000000
 , 0x0000000000000000
 , 0x0000000000000000
 };

uint64_t d[NLIMBS] =
 { 0x3301a94c920f1401
 , 0xa5ce65f4ac505540
 , 0x371015f103d36561
 , 0xaef9b1cb4dc7dd4c
 , 0x2bf3c2dd9dab6333
 , 0xd8c6cd42fef697c2
 , 0x45fb1e9c2fe4f11f
 , 0x976a220e1b8df884
 , 0xe74f8ae02ebfe893
 , 0x738a1f49bab32eb0
 , 0x9525b641bb34708d
 , 0x145cebd06564c9af
 , 0x2d258af688c45c14
 , 0x17dde7f87432bb9a
 , 0x3172fb15a80ee3a8
 , 0x7f6fea75cf31df57
 };

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
  bn_print("t=", x);
  fp_toM(x, x);
  bn_print("tM=", x);
  fp_exp(y, x, e);
  bn_print("cM=", y);
  fp_exp(x, y, d);
  bn_print("tM=", x);
  fp_fromM(x, x);
  bn_print("t=", x);
}
