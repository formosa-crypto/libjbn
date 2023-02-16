#include <string.h>
#include <stdint.h>
#include <assert.h>
#include <gmp.h>

#include "expm.h"

extern void fp_toM(
  uint64_t *rp,
  uint64_t *ap
);

extern void fp_fromM(
  uint64_t *rp,
  uint64_t *ap
);

extern void fp_expm_noct(
  uint64_t *rp,
  uint64_t *ap,
  uint64_t *bp
);

void expm_test(uint64_t *result, uint64_t *base, uint64_t *exp, uint64_t *mod)
{
  uint64_t baseM[NLIMBS];
  fp_toM(baseM, base);
  fp_expm_noct(result, baseM, exp);
  fp_fromM(result, result);
}
