#include "api.h"
#include "xstr.h"
#include "namespace.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//

#ifndef NLIMBS
#define NLIMBS NAMESPACE(NLIMBS)
#endif

extern void fp_add(uint64_t*, uint64_t*, uint64_t*);
extern void fp_sub(uint64_t*, uint64_t*, uint64_t*);
extern void fp_mul(uint64_t*, uint64_t*, uint64_t*);
extern void fp_sqr(uint64_t*, uint64_t*);
extern void fp_expm_noct(uint64_t*, uint64_t*, uint64_t*);
extern void fp_inv(uint64_t*, uint64_t*);
extern void fp_toM(uint64_t*, uint64_t*);
extern void fp_fromM(uint64_t*, uint64_t*);

// TODO

//

#include "cpucycles.c"
#include "printbench.h"

//

int fn_generic_main(void)
{
  #define LOOPS 5
  #define TIMINGS 4096
  #define OP 8

  int loop, i, op;
  char *op_str[OP] = {
    xstr(fp_add,.csv),
    xstr(fp_sub,.csv),
    xstr(fp_mul,.csv),
    xstr(fp_sqr,.csv),
    xstr(fp_expm_noct,.csv),
    xstr(fp_inv,.csv),
    xstr(fp_toM,.csv),
    xstr(fp_fromM,.csv)
  };
  uint64_t cycles[TIMINGS];
  uint64_t results[OP][LOOPS];

  uint64_t a[NLIMBS*2], b[NLIMBS*2], c[NLIMBS*2];
  uint64_t r;

  for(loop = 0, op=0; loop < LOOPS; loop++, op=0)
  {
    // fp_add
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_add(a, b, c); }
    results[op++][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_sub
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_sub(a, b, c); }
    results[op++][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_mul
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_mul(a, b, c); }
    results[op++][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_sqr
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_sqr(a, b); }
    results[op++][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_expm_noct
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_expm_noct(a, b, c); }
    results[op++][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_inv
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_inv(a, b); }
    results[op++][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_toM
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_toM(a, b); }
    results[op++][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_fromM
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_fromM(a, b); }
    results[op++][loop] = cpucycles_median(cycles, TIMINGS);
  }

  cpucycles_fprintf_2(results, op_str);

  return 0;

  #undef OP
  #undef TIMINGS
  #undef LOOPS
}

