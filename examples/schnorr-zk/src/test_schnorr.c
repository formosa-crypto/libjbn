#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <assert.h>

#include "schnorr_protocol.h"


/* Example witness.
 ex_w = 13562074942232698298179099715097584669743616762010001864533299997056731796296371039510377235748195022542024618898643826330807122904488341755722122148636711055263632491105526304501244287463084252119549757055178218173913102047978750988651708456497584278036673201887047222348131014704171051451256673650666629515213300997703806314646378361492063336814804438811067630413966929471013613663155038542386255423974557632334836982678865780618968772883384376382351839231415319749576574591601796022013741069051949170875806063999540180799183260929359622774470129812372649035895482951427131973688235088596275593114503240007521869714 */
uint64_t ex_w[NLIMBS] =
 {0xdf2698bc2b431f92,
  0x89565fb2f5d4f2a2,
  0x8717f166e2df52f0,
  0x25c18110b4d92652,
  0x4b3fe60672a04b65,
  0x57384c17581db539,
  0x31920d01b8cd5e78,
  0x7b7e1e0247a96ffa,
  0x17a69a1e9ea585bc,
  0xc1ad5b44032c2b36,
  0x0eec728a4b3a3896,
  0xd942364ebec75442,
  0xbb35bcf9893bafad,
  0x7e2cdcbf4380450b,
  0xcdefe3e560f2de9e,
  0x212ede04b32895de,
  0x7ab1d1c24651d7a0,
  0x7045c322c6b0cf79,
  0x81714ef9efe70bf8,
  0xd528cb67b4249ea6,
  0x026d047229d001d5,
  0x858611d321f5816d,
  0x8e436d7699ea19be,
  0x942eb3f1704dbb2b,
  0x605316f096204980,
  0xe7db4c22b147c9fd,
  0xde00e0c7628aee5f,
  0x1a94670c1d75a239,
  0x0eed85c743402d4f,
  0x3fe8ee89eefd8fff,
  0xbe77744343bc8cb5,
  0x6b6ead0684a3e5bd
 };
/*
 { 16079707453520027538ull
 , 9896202453426434722ull
 , 9734514543779861232ull
 , 2720597558662080082ull
 , 5422305391744666469ull
 , 6284856943141827897ull
 , 3571931755504819832ull
 , 8898582908871733242ull
 , 1704218965307655612ull
 , 13955911167960165174ull
 , 1075360349327866006ull
 , 15655134966529348674ull
 , 13489896038793457581ull
 , 9091884461783532811ull
 , 14839329871522619038ull
 , 2391092563947328990ull
 , 8841078175838623648ull
 , 8090086859770744697ull
 , 9327323138639727608ull
 , 15359750175411445414ull
 , 174800848911598037ull
 , 9621397252429152621ull
 , 10251157532981205438ull
 , 10677669616094657323ull
 , 6940916673274726784ull
 , 16707030954547857917ull
 , 15997033023376387679ull
 , 1915269043270820409ull
 , 1075662976884682063ull
 , 4605192895173857279ull
 , 13724566221682937013ull
 , 7741315053003204029ull
 };
*/
/* Example statement.
 ex_s = 17448105564697743235596200779905060886140102301589836974870836993584491604725980549786805891101128905392483202643612799832388966813381742461470387725541672947131967359215271192071104242818534618159207393267571342157931998220631680702975123830881219215736803556617335999518588338804520261434697814567055925964501568025260046973303129822355476335079189622119622697775023077959076699091477716959124081583302657743773751866109946017718536963183669118715561381915446592752262392261234321714414999399944719644372451141711218530146601499574810057491831816916583316009757172316828411111743676667730848241028554193006466552845 */
uint64_t ex_s[NLIMBS] =
 {0x6387f406eb01d40d,
  0x7a30dddeaf33c61f,
  0xca8a1261ec2be3c0,
  0x146efd311b320343,
  0x44abaa9f2aed215a,
  0x0e507d77a6893537,
  0x4292777ee5c658ee,
  0xe8a76cb7b15d8d12,
  0x4d8056059405d844,
  0xa93659e0f6c17e01,
  0x38f867d35447058c,
  0xf01090334c0fa0c3,
  0xc254f3cdc8ba7e94,
  0x0d6d47096524123f,
  0x557c7985ba77ec23,
  0xf4b22c6c315ff71c,
  0xf263a6304408ee58,
  0x7c3434a189bc27d5,
  0xe9bbf78704f8ba39,
  0xb1a8ca466211c641,
  0x15be97cea29519b4,
  0x9ef7c28991c103d2,
  0xadafad8a90a620bb,
  0xa2e5e18c915d0823,
  0x5a5671f771e1c47a,
  0x38b83666ca8d8a17,
  0x209c657d0d8f8263,
  0xd8305083e9ceaf72,
  0xd61016d7afd0addd,
  0x2efb2fb0e24280c6,
  0x12d75e07199ad7e2,
  0x8a3732dc2206a587
 };
/*
 { 171969242160550925ull
 , 804781220001203743ull
 , 4594497754230940608ull
 , 472392515548218179ull
 , 948236216193327450ull
 , 31462267516433719ull
 , 797027940007565550ull
 , 6764487674120473874ull
 , 584558119897651268ull
 , 2193031863899618817ull
 , 105145217697908108ull
 , 7298484718723899587ull
 , 4003085206563225236ull
 , 67507600631665215ull
 , 159932005602028579ull
 , 7632204334305376028ull
 , 7465986506102992472ull
 , 949836227897206741ull
 , 6842327390758156857ull
 , 2801704344442488385ull
 , 566856634118248884ull
 , 1454838073351799762ull
 , 2515412700129796283ull
 , 1738035997661530147ull
 , 509515618992112762ull
 , 87076476951562775ull
 , 349864693353382499ull
 , 5578039638568120178ull
 , 5424853839367417309ull
 , 385351981655818438ull
 , 357657197262854114ull
 , 959485021998196103ull
 };
*/

void bn_print(char* str, uint64_t x[]) {
 int i;
 if (str!=NULL) printf("%s = [ ", str);
 for (i=0; i<NLIMBS; i++) {
   if (0 < i) printf(", ");
   printf("0x%016" PRIx64 "", x[i]);
 }
 printf("]\n");
}



void print(char* str, uint64_t *array)
{
  int i;
  if (str!=NULL) printf("%s = [ ", str);
  for(i=0; i<(NLIMBS-1); i++)
  { printf("0x%016" PRIx64 ", ", array[i]); }
  printf("0x%016" PRIx64 "\n", array[NLIMBS-1]);
}



typedef uint64_t bignum[NLIMBS];

int main(void)
{
  bignum commitment_p, random_power_p, challenge_p, response_p;
  uint64_t result_p[1];

  printf("\n*** Prover commits ***\n");
  commitment(commitment_p, random_power_p);
  bn_print("COMMITMENT (Mont. form)", commitment_p);
  bn_print("\nSECRET POWER:\n",random_power_p);

  printf("\n*** Verifier challenges ***\n");
  challenge(challenge_p);
  bn_print("CHALLENGE", challenge_p);

  printf("\n*** Prover responds ***\n");
  response(ex_w, random_power_p, challenge_p, response_p);
  bn_print("RESPONSE",response_p); 

  printf("\n*** Verifier decides ***\n");
  verify(ex_s, commitment_p, challenge_p, response_p, result_p);
  printf("CHECK = 0x%02" PRIx64 "\n\n", result_p[0]);

  return 0;
}