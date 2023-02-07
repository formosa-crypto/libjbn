#ifndef TEST_MISC_PRIMES
#define TEST_MISC_PRIMES

#include <stdint.h>
#include <gmp.h>

void primes_clear_bit(uint64_t *dest, size_t index);

void primes_seed(uint64_t **dest, int dest_init, size_t NLIMBS, size_t clear_bits_from_the_top);

int primes_P(uint64_t **_P, int dest_init, int dest_print, FILE *fout, size_t NLIMBS);

#endif
