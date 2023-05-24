#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <gmp.h>

#include "params.h"
#include "randombytes.h"
#include "primes.h"


void primes_clear_bit(uint64_t *dest, size_t index)
{
  uint64_t mask = ~(((uint64_t)1) << (index & 0x3f));
  dest[index >> 6] &= mask;
}


void primes_seed(uint64_t **dest, int dest_init, size_t NLIMBS, size_t clear_bits_from_the_top)
{
  uint64_t *dest_tmp;

  if(dest_init == 1)
  { *dest = calloc(NLIMBS, sizeof(uint64_t)); }

  dest_tmp = *dest;
  randombytes((uint8_t*) dest_tmp, NLIMBS*sizeof(uint64_t));
  dest_tmp[0] |= 1; // make it odd

  while(clear_bits_from_the_top > 0)
  { primes_clear_bit(dest_tmp, (NLIMBS*64) - clear_bits_from_the_top);
    clear_bits_from_the_top--;
  }
}


int primes_P(uint64_t **_P, int dest_init, int dest_print, FILE *fout, size_t NLIMBS)
{
  // Miller-Rabin tests
  #define MRT 30

  int found;
  size_t clear_bits_from_the_top = 1; // one bit clear on the top from the start
  mpz_t P, P2, R, gcd, one;

  // R = 2^(NLIMBS*64)
  params_set_R(R, NLIMBS);

  // set gcd to 0 and one to 1
  mpz_init_set_ui(gcd, 0);
  mpz_init_set_ui(one, 1);
  mpz_init2(P2, (NLIMBS+1)*64);

  // "seed" and test P
  primes_seed(_P, dest_init, NLIMBS, clear_bits_from_the_top);
  params_load(P, 1, *_P, NLIMBS);

  found = 0;
  do
  {
     // check probability of mpz_probab_prime_p returning > 0 after primes seeed (intuitively is low)
     mpz_nextprime(P, P);

     // check if 2*P < R
     mpz_mul_2exp(P2, P, 1);
     if(mpz_cmp(P2, R) >= 0) // "returns a positive value if op1 > op2 ; zero if op1 = op2 ; negative value if op1 < op2"
     { // if this condition isn't met, get a different seed with one bit less
       clear_bits_from_the_top += 1;
       primes_seed(_P, 0, NLIMBS, clear_bits_from_the_top);
       params_load(P, 0, *_P, NLIMBS);
       continue;
     }

     // test if gcd(P,R) == 1 // after mpz_nextprime it should be, considering R, nonetheless leave the code 'generic'.
     mpz_gcd(gcd, P, R);
     if(mpz_cmp(gcd, one) != 0)
     { continue; }

     // test P with mpz_probab_prime_p
     found = mpz_probab_prime_p(P, MRT);
  }
  while(found < 0);

  if(dest_print == 1)
  { gmp_fprintf(fout, "0x%Zx\n", P); }

  params_store(*_P, NLIMBS, P, 1, "prime_P");
  mpz_clears(R, gcd, one, P2, NULL);
  return found;

  #undef MRT
}

#ifdef _MAIN_PRIMES
int main(int argc, char** argv)
{
  uint64_t *P;
  size_t i, NLIMBS, n;

  // check argc and load NLIMBS
  if(argc != 3)
  { fprintf(stderr, "usage:   ./primes NLIMBS NUMBER_OF_PRIMES\n");
    fprintf(stderr, "example: ./primes 4 10\n");
    return -1;
  }

  NLIMBS = strtoull(argv[1], NULL, 0);
  assert(NLIMBS >= 1 && NLIMBS <= 256);

  n = strtoull(argv[2], NULL, 0);

  for(i=0; i<n; i++)
  { primes_P(&P, 1, 1, stdout, NLIMBS);
    free(P);
  }

  return 0;
}
#endif

