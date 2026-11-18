#include <stdio.h>
#include <stdint.h>
#include <assert.h>

//#include "libjbn_fp.h"
#include <stdint.h>
extern uint64_t bn_muln(uint64_t*, uint64_t*, uint64_t*);
extern uint64_t bn_muln_reg(uint64_t*, uint64_t*, uint64_t*);


#define NLIMBS 5

uint64_t t[5] =
 { 0x85ec8a8a05a6a277
 , 0xb2b0e63bd8e45521
 , 0x66912e26efccc253
 , 0x0567d2df32a3e558
 , 0xdb1c95ff0c6a3807
 };
uint64_t tt[10] =
 { 0xf057631bbf6ed351
 , 0x76cafbad7423913a
 , 0xf0d8d5a0db92106f
 , 0xf4e0c138a72af97d
 , 0x8614a2effc24d0e1
 , 0x0b59be90d54cf9c5
 , 0xf1fce39e105618af
 , 0x5bf05628d127eac4
 , 0xa636bd1abc5ab027
 , 0xbb89ebd386eb55a5
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
