#include <string.h>
#include <stdint.h>
#include <assert.h>
#include <gmp.h>

#include "cpucycles.c"

extern void fp_toM(
  uint64_t *rp,
  uint64_t *ap
);

extern void fp_fromM(
  uint64_t *rp,
  uint64_t *ap
);

extern void fp_exp(
  uint64_t *rp,
  uint64_t *ap,
  uint64_t *bp
);

uint64_t exp_bench(uint64_t *result, uint64_t *base, uint64_t *exp, uint64_t *mod)
{
  uint64_t baseM[NLIMBS];
  uint64_t cycles_start, cycles_end, cycles_total;

  fp_toM(baseM, base);

  cycles_start = cpucycles();
  fp_exp(result, baseM, exp);
  cycles_end = cpucycles();

  fp_fromM(result, result);

  cycles_total = cycles_end - cycles_start;
  return cycles_total;
}
