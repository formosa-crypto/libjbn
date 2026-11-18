#include <stdio.h>
#include <stdint.h>
#include <assert.h>

//#include "libjbn_fp.h"
#include <stdint.h>
extern uint64_t bn_muln_os(uint64_t*, uint64_t*, uint64_t*);
extern uint64_t bn_muln_ps(uint64_t*, uint64_t*, uint64_t*);
extern uint64_t bn_kar(uint64_t*, uint64_t*, uint64_t*);


#define NLIMBS 24

uint64_t t[24] =
 { 0x7184ce892dcd97ed
 , 0x3cd9b4ce8274e72a
 , 0x0ef5a428cd39de9f
 , 0xdb87471aad1c788c
 , 0x13344a3501341e8b
 , 0x7cc9b274f40a6c84
 , 0xda994936a689af50
 , 0x56fe18c3a99906f9
 , 0x43549191bdadd8a7
 , 0xf8a4764a3dc3e0f5
 , 0x2ea31b65f5d55876
 , 0x0554ab5d6f3fc70a
 , 0x369fe8b395350131
 , 0xb8f1b1bbc95e7fe3
 , 0x11efe094a11356fa
 , 0x1606ab95d4a9740e
 , 0x2a8f2811348c596f
 , 0xba9873ab6580d41d
 , 0x24422e360931c190
 , 0x1494fcc722f31ec8
 , 0x0bc287df6d75202c
 , 0x0b56a827cf2a26ce
 , 0x6ff8d143643a8d85
 , 0xf1e63d300299e37e
 };
uint64_t tt[48] =
 { 0xd527f42ffdbb7169
 , 0x19cbf2f130f35b20
 , 0xdf06a2d80320795d
 , 0x7689ffe4e6a5d905
 , 0xa351879582398249
 , 0x0de521cb934f62e9
 , 0xf4ff5e09ff64a7e1
 , 0xd70a5bf5e32a5869
 , 0x9799fa0827d8255f
 , 0x446945c4efd1d267
 , 0x6be8ac7eb19ff6ff
 , 0xa5348e2b8f24f384
 , 0xb4e1bfa8b20fd02f
 , 0x5aab77182ecbb1b8
 , 0x867a0ff114dbacf9
 , 0xa74746515f47eb48
 , 0x89f37bba64b9d752
 , 0x5b7b4c6027c93de7
 , 0xa19ef6950cf07003
 , 0xae0d021679874ea8
 , 0x11553d6690dcdefe
 , 0x01d282d70b997fd6
 , 0xcc222048419a969a
 , 0x753777053e516d54
 , 0xba0f2a66992e3ec6
 , 0xf66ff4445da14e74
 , 0x3e68172fe4fc0f67
 , 0x99cc42ba845f9686
 , 0x08b08d665ef38727
 , 0x48e9b67354626bff
 , 0xaaf6355e27ccfd67
 , 0xca479b67de140ab5
 , 0x77bd49df986fdb27
 , 0x2b521e74387abed3
 , 0x85c675d135de51d8
 , 0x85134b0a0db4ab8a
 , 0x84c504c6700d3cf9
 , 0x4e5fa7204623bfed
 , 0x6fe855e10223bbff
 , 0x875262cfe3173e18
 , 0xbf5ebc8669acdf61
 , 0xc33a391aebc54a76
 , 0x73c69b1f04a5243d
 , 0xccf1631858ea47ac
 , 0xb396c7a45820f600
 , 0x24f3f334f495e14e
 , 0x262a01ef29e22269
 , 0xe4934e4665ca5517
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
  int i;
  for (i=0; i<10000000; i++) {
    bn_muln_ps(x, t, t);
  }
  bn2_check("mul_kar", tt, x);
//  bn_muln_reg(x, t, t);
//  bn2_check("muln_reg", tt, x);
  return 0;
}
