#include "api.h"
#include "namespace.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//

#define NLIMBS NAMESPACE(NLIMBS)

extern void bn_eq(uint64_t*, uint64_t*);
extern void bn_test0(uint64_t*);
extern void bn_copy(uint64_t*, uint64_t*);
extern void bn_set0(uint64_t*);
extern void bn_addn(uint64_t*, uint64_t*, uint64_t*);
extern void bn_subn(uint64_t*, uint64_t*, uint64_t*);
extern void bn_muln(uint64_t*, uint64_t*, uint64_t*);
extern void bn_sqrn(uint64_t*, uint64_t*);

extern void fp_add(uint64_t*, uint64_t*, uint64_t*);
extern void fp_sub(uint64_t*, uint64_t*, uint64_t*);
extern void fp_mul(uint64_t*, uint64_t*, uint64_t*);
extern void fp_sqr(uint64_t*, uint64_t*);
extern void fp_expm_noct(uint64_t*, uint64_t*, uint64_t*);
extern void fp_inv(uint64_t*, uint64_t*);
extern void fp_toM(uint64_t*, uint64_t*);
extern void fp_fromM(uint64_t*, uint64_t*);

//

#define xstr(s,e) str(s)#e
#define str(s) #s

//

#ifndef LOOPS
#define LOOPS 3
#endif

#ifndef TIMINGS
#define TIMINGS 2048
#endif

#define OP 16

//

#include "cpucycles.c"
#include "printbench.c"

//

int main(void)
{
  int loop, i;
  char *op_str[] = {
    xstr(bn_eq,.csv),
    xstr(bn_test0,.csv),
    xstr(bn_copy,.csv),
    xstr(bn_set0,.csv),
    xstr(bn_addn,.csv),
    xstr(bn_subn,.csv),
    xstr(bn_muln,.csv),
    xstr(bn_sqrn,.csv),
    xstr(fp_add,.csv),
    xstr(fp_sub,.csv),
    xstr(fp_mul,.csv),
    xstr(fp_sqr,.csv),
    xstr(fp_expm_noct,.csv),
    xstr(fp_inv,.csv),
    xstr(fp_toM,.csv),
    xstr(fp_fromM,.csv)
  };

  uint64_t a[NLIMBS*2], b[NLIMBS*2], c[NLIMBS*2];

  uint64_t cycles[TIMINGS];
  uint64_t results[OP][LOOPS];

  for(loop = 0; loop < LOOPS; loop++)
  {
    // bn_eq 
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      bn_eq(a, b); }
    results[0][loop] = cpucycles_median(cycles, TIMINGS);

    // bn_test0
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      bn_test0(a); }
    results[1][loop] = cpucycles_median(cycles, TIMINGS);

    // bn_copy
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      bn_copy(a, b); }
    results[2][loop] = cpucycles_median(cycles, TIMINGS);

    // bn_set0
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      bn_set0(a); }
    results[3][loop] = cpucycles_median(cycles, TIMINGS);

    // bn_addn
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      bn_addn(a, b, c); }
    results[4][loop] = cpucycles_median(cycles, TIMINGS);

    // bn_subn
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      bn_subn(a, b, c); }
    results[5][loop] = cpucycles_median(cycles, TIMINGS);

    // bn_muln
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      bn_muln(a, b, c); }
    results[6][loop] = cpucycles_median(cycles, TIMINGS);

    // bn_sqrn
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      bn_sqrn(a, b); }
    results[7][loop] = cpucycles_median(cycles, TIMINGS);

    // ////////////////////////////////////////////////////

    // fp_add
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_add(a, b, c); }
    results[8][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_sub
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_sub(a, b, c); }
    results[9][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_mul
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_mul(a, b, c); }
    results[10][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_sqr
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_sqr(a, b); }
    results[11][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_expm_noct
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_expm_noct(a, b, c); }
    results[12][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_inv
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_inv(a, b); }
    results[13][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_toM
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_toM(a, b); }
    results[14][loop] = cpucycles_median(cycles, TIMINGS);

    // fp_fromM
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      fp_fromM(a, b); }
    results[15][loop] = cpucycles_median(cycles, TIMINGS);
  }

  cpucycles_fprintf_2(results, op_str);

  return 0;
}

