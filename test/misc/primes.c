#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <gmp.h>

#include "gen.h"
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
  //memset(dest_tmp, 0xff, NLIMBS*sizeof(uint64_t));
  dest_tmp[0] |= 1;

  while(clear_bits_from_the_top > 0)
  { primes_clear_bit(dest_tmp, (NLIMBS*64) - clear_bits_from_the_top);
    clear_bits_from_the_top--;
  }
}

int primes_P(uint64_t **_P, int dest_init, int dest_print, FILE *fout, size_t NLIMBS)
{
  // Miller-Rabin tests
  #define MRT 30

  int found = 0;
  size_t clear_bits_from_the_top = 0;
  mpz_t R, gcd, one, P;

  // R = 2^(NLIMBS*64) 
  gen_set_R(R, NLIMBS);

  // set gcd to 0 and one to 1
  mpz_init_set_ui(gcd, 0);
  mpz_init_set_ui(one, 1);

  // "seed" and test P
  primes_seed(_P, dest_init, NLIMBS, clear_bits_from_the_top);
  gen_load(P, 1, *_P, NLIMBS);
  found = mpz_probab_prime_p(P, MRT);

  while(found < 1) // mpz_probab_prime_p returns: 0 definitely not prime; 1 probably prime; 2 definitely prime;
  {
    mpz_nextprime(P, P);
    found = mpz_probab_prime_p(P, MRT);

    if( mpz_sizeinbase(P,2) > NLIMBS*64 )
    { clear_bits_from_the_top += 1;
      primes_seed(_P, 0, NLIMBS, clear_bits_from_the_top);
      gen_load(P, 0, *_P, NLIMBS);
      found = mpz_probab_prime_p(P, MRT);
    }
  }

  if(dest_print == 1)
  { gmp_fprintf(fout, "0x%Zx\n", P); }

  gen_store(*_P, NLIMBS, P, 1, "prime_P");
  mpz_clears(R, gcd, one, NULL);
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
  { fprintf(stderr, "usage:   ./gen NLIMBS NUMBER_OF_PRIMES\n");
    fprintf(stderr, "example: ./gen 4 10\n");
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








