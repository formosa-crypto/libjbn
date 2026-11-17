#include <stdio.h>
#include <stdint.h>
#include <assert.h>

//#include "libjbn_fp.h"
#include <stdint.h>
extern uint64_t bn_muln_os(uint64_t*, uint64_t*, uint64_t*);
extern uint64_t bn_muln_ps(uint64_t*, uint64_t*, uint64_t*);


#define NLIMBS 12

uint64_t t[12] =
 { 0x7863739fe4509285
 , 0x1fa11078c542ecc7
 , 0x4288a85053246218
 , 0x0b71d2a42c985067
 , 0x8bdefdacbd7f5071
 , 0x86b5166532556b15
 , 0xa70ff5eae14f0028
 , 0x48e3f2abb18d886a
 , 0x53ba55b7372b5990
 , 0xa29130ef6befd2c0
 , 0x0a6951cd1b95ecd8
 , 0x18e0749f75a26b72
 };
uint64_t tt[24] =
 { 0xce371d8ecefbf919
 , 0x1363aa4e49ec2d71
 , 0xa48f30a357ede4d4
 , 0x8ee38b21fe9c6373
 , 0x3e94f60185da7e3a
 , 0xd35ca468ce20cd04
 , 0xb673409bade342ae
 , 0x3b4082f135422d19
 , 0xa195bdf102255fe3
 , 0xa3b2587e912789ad
 , 0xc4f98b8a3d12e1f0
 , 0x4e52a92ce7e24d9f
 , 0x5bd6654033a81129
 , 0x45809fc7534a08bb
 , 0x4a6e735b26619f82
 , 0xa8659f57d1f7d645
 , 0x55dbeb15beb56992
 , 0x805b631822bcc0bb
 , 0xb09807674ec28909
 , 0x54ce0f36f0d09ecd
 , 0x82712d16b5c11d0a
 , 0x8fe0e961f2c3e508
 , 0xf0b4a6006403da21
 , 0x026adaaa323d364f
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

int test_eq(int size, uint64_t x[], uint64_t y[]) {
  int i;
  int r = 1;
  for (i=0; i < size; i++)
    r = r && (x[i]==y[i]);
  return r;
}

int bn2_check(char* str, uint64_t x[], uint64_t y[]) {
  int r = test_eq(2*NLIMBS,x,y);
  printf("TESTING %s: \n", str);
  if (! r ) {
    printf("Expecting: ");
    bn2_print("", x);
    printf(", but got: ");
    bn2_print("", y);
  } else {
    printf("...OK!\n");
  }
  return r;
}

int main() {
  uint64_t x[2*NLIMBS];
  bn_muln(x, t, t);
  bn2_check("muln", tt, x);
  bn_muln_reg(x, t, t);
  bn2_check("muln_reg", tt, x);
  return 0;
}
