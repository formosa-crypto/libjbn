#include <string.h>
#include <stdint.h>
#include <assert.h>
#include <gmp.h>

#include "exp.h"

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

void exp_test(uint64_t *result, uint64_t *base, uint64_t *exp, uint64_t *mod)
{
  uint64_t baseM[NLIMBS];
  fp_toM(baseM, base);
  fp_exp(result, baseM, exp);
  fp_fromM(result, result);
}
