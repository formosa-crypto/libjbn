#include <stdio.h>
#include <stdint.h>
#include <assert.h>

//#include "libjbn_fp.h"
#include <stdint.h>
extern uint64_t bn_ps_muln(uint64_t*, uint64_t*, uint64_t*);
extern uint64_t bn_os_muln(uint64_t*, uint64_t*, uint64_t*);
extern uint64_t bn_kar_muln(uint64_t*, uint64_t*, uint64_t*);


#define NLIMBS 32

uint64_t t[32] =
 { 0xfd21f4ed531c1001
 , 0xc9bb74a3d5f1bc0c
 , 0x114a28a58344cb79
 , 0x7017abd43ece2fd9
 , 0xfa2714b0e3aec5d0
 , 0x65810db43c135c21
 , 0x94e3303fae3bc06c
 , 0x4c1795b0f276a8d8
 , 0x256f11e69f2451ec
 , 0x4784a95025584d49
 , 0xdb66d5489e3a044f
 , 0x5bfa0174d8cbd413
 , 0xe7bf5e13f947fcff
 , 0xcf2dda20f9038563
 , 0xd1a6d273d2344d6f
 , 0xb3d27d7bdc048ddf
 , 0xad4976845890454d
 , 0x391765a152cfff39
 , 0xd1b42f83b1498f62
 , 0x0e4fa3a3b819caec
 , 0x43e3eb121b0b35e1
 , 0xcd6ac2b8c16b0aed
 , 0xe3257bbb8c03bc51
 , 0x49528489e8c0d92e
 , 0x2a8962ebac83f7d2
 , 0xe4e0dc790f524c62
 , 0x617a4ecd38d4bdba
 , 0x29d8fdc3faeafd21
 , 0xcda511a7b237a1a9
 , 0xeec07059caeafd7a
 , 0x402babd0f897da20
 , 0xe36cb65b684465a4
 };
uint64_t tt[64] =
 { 0x95b4bf4e27382001
 , 0xe00e21acf3cf1f66
 , 0xc6f442156eb15c90
 , 0xa865eeeb2cc9cd93
 , 0x0da8d6a1a4e5e4a2
 , 0x876845a4f4dd0d4b
 , 0x35f34d9b6002321d
 , 0xf552ffb9d8f36bb5
 , 0xc577b8f9292ef8c8
 , 0x9b0ca683e6d63ea1
 , 0x0a7b088106318a1a
 , 0xf5e1e80d57d71f56
 , 0xa9416f1faf7bb6ad
 , 0x0e1726de252bd874
 , 0xae61209943262154
 , 0x02ad0021764ed4f3
 , 0x111774509ad1271e
 , 0xadec8c751b8a1d11
 , 0x03385deb81afc746
 , 0x24af448cbb464e51
 , 0xd6b2e0ae6e346543
 , 0xebfac6b90fe6d1f7
 , 0x4071c6e87021962b
 , 0xc14e303337a7226b
 , 0x6f5994f9bf24bc62
 , 0xd40585c415046135
 , 0x055eaabd7ec9dff2
 , 0x41dafe970f6ec52d
 , 0x7020d9e19a830d9c
 , 0xfd44f69f9fd5379b
 , 0x50b29f8945e310e7
 , 0xf4fa41292de3cb27
 , 0xe41b072bb5058df4
 , 0x0d04703eb0cbbe72
 , 0x991bfa7ac48c6403
 , 0x423badccc6889752
 , 0xb37b63159dcfdbae
 , 0x6c356ed97256d395
 , 0x02ba2f94ede48603
 , 0x08f63ebd5d6ed8f1
 , 0xed2a53d87822d5e4
 , 0xbde0dc080a7f4843
 , 0x556c6912253057ff
 , 0xfb27a1d3f1d8c36a
 , 0xa554089e096f3b45
 , 0x9ca2be4d5fd0eb9c
 , 0x49df576d8ecfaa25
 , 0x09cde6829d1818c1
 , 0xbf48a5f3aee5f24b
 , 0xeee4ed1b0b03a12e
 , 0x492d81bf03aa239c
 , 0x8dd01ae06f92a2dd
 , 0x5507019eccab273e
 , 0xf7ab093ef073e8cb
 , 0xa8c1a328e426c34f
 , 0x2764e40370aaf27f
 , 0x25aa161b74fcc505
 , 0x6565242245c98ab0
 , 0x2972a73aeea5575a
 , 0x9d720fc794780358
 , 0xf3960c3d9b25dc24
 , 0xe7eaf7aa06286f07
 , 0x98010a6ce448ebd0
 , 0xca09f99079ef5edb
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
    bn_kar_muln(x, t, t);
  }
  bn2_check("mul_kar_32_ps_4", tt, x);
  return 0;
}
