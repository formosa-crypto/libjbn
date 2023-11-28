#include <string.h>
#include <stdint.h>
#include <gmp.h>

#include "cpucycles.c"

uint64_t exp_bench(uint64_t *result, uint64_t *base, uint64_t *exp, uint64_t *mod)
{
  mpz_t m_result, m_base, m_exp, m_mod;
  size_t result_count;
  uint64_t cycles_start, cycles_end, cycles_total;

  // clear output pointer
  memset(result, 0, sizeof(uint64_t)*NLIMBS);

	mpz_init2(m_result, NLIMBS*64);
	mpz_init2(m_base, NLIMBS*64);
	mpz_init2(m_exp, NLIMBS*64);
	mpz_init2(m_mod, NLIMBS*64);

  /**
  void mpz_import (mpz_t rop, size_t count, int order, size_t size, int endian, size_t nails, const void *op)
    count: number of words;
    order: 1 most significant word first; -1 least significant word first;
    size: size of each word;
    endian: 1 most significant byte first; -1 least significant byte first; 0 native;
    nails: number of most significant bits that are skipped, 0 means use the full word;
  **/

  mpz_import(m_base, NLIMBS, -1, sizeof(uint64_t), 0, 0, base);
  mpz_import(m_exp,  NLIMBS, -1, sizeof(uint64_t), 0, 0, exp);
  mpz_import(m_mod,  NLIMBS, -1, sizeof(uint64_t), 0, 0, mod);

  /**
  void mpz_powm (mpz_t rop, const mpz_t base, const mpz_t exp, const mpz_t mod)
  **/
  cycles_start = cpucycles();
	mpz_powm_sec(m_result, m_base, m_exp, m_mod);
  cycles_end = cpucycles();


  /**
  void * mpz_export (void *rop, size_t *countp, int order, size_t size, int endian, size_t nails, const mpz_t op)
  **/
  mpz_export(result, &result_count, -1, sizeof(uint64_t), 0, 0, m_result);

  mpz_clears(m_result,m_base,m_exp,m_mod,NULL);

  cycles_total = cycles_end - cycles_start;
/*printf("%lld\n", cycles_total);*/

  return cycles_total;
}

