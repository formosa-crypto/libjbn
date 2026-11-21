#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <gmp.h>

//
#define OP1 1

//

#include "xstr.h"
#include "config.h"
#include "cpucycles.c"
#include "printbench.c"
#include "alignedcalloc.c"
#include "benchrandombytes.c"
#include "stability.c"

//
extern uint64_t glob_p[NLIMBS];
uint64_t exp_bench(uint64_t *result, uint64_t *base, uint64_t *exp, uint64_t *mod);
//

// base = base % mod
void reduce(uint64_t *base, uint64_t *mod)
{
  uint64_t *r;
  mpz_t m_base, m_mod;
  size_t base_count;

  // init and load
	mpz_init2(m_base, NLIMBS*64);
	mpz_init2(m_mod,  NLIMBS*64);

  mpz_import(m_base,  NLIMBS, -1, sizeof(uint64_t), 0, 0, base);
  mpz_import(m_mod,   NLIMBS, -1, sizeof(uint64_t), 0, 0, mod);

  mpz_mod(m_base, m_base, m_mod);

  memset(base, 0, NLIMBS*sizeof(uint64_t));
  r = mpz_export(base, &base_count, -1, sizeof(uint64_t), 0, 0, m_base);
  mpz_clears(m_base, m_mod,NULL);

  assert( r == base );
  assert( base_count <= NLIMBS);
}

int main(int argc, char**argv)
{
  size_t run, loop, i;
  uint64_t cycles[TIMINGS];
  uint64_t median_loops[OP1][LOOPS];

#if defined(ST_ON)
  uint64_t median_runs[OP1][RUNS];
  double   sd_runs[OP1], mean_runs[OP1];
#endif

  char *op1_str[] = {xstr(exp,.csv) };

  char *op1_str_short[] = { "exp" };

  uint64_t *_result, *result;
  uint64_t *_base, *base;
  uint64_t *_exp, *exp;
  uint64_t *_mod, *mod;

  pb_init_1(argc, op1_str);

  result = (uint64_t*) alignedcalloc((uint8_t**)&_result, NLIMBS*sizeof(uint64_t));
  base   = (uint64_t*) alignedcalloc((uint8_t**)&_base,   NLIMBS*sizeof(uint64_t));
  exp    = (uint64_t*) alignedcalloc((uint8_t**)&_exp,    NLIMBS*sizeof(uint64_t));
  mod    = (uint64_t*) alignedcalloc((uint8_t**)&_mod,    NLIMBS*sizeof(uint64_t));

  // init mod
  memcpy(mod, glob_p, NLIMBS*sizeof(uint64_t));

_st_while_b

  for(run = 0; run < RUNS; run++)
  {
    _st_reset_randombytes

    for(loop = 0; loop < LOOPS; loop++)
    {
      benchrandombytes((uint8_t*)exp, NLIMBS*sizeof(uint64_t));
      benchrandombytes((uint8_t*)base, NLIMBS*sizeof(uint64_t));
      reduce(base, mod);

      // exp_bench
      for (i = 0; i < TIMINGS; i++)
      { cycles[i] = exp_bench(result, base, exp, mod); }

      median_loops[0][loop] = median(cycles, TIMINGS);
    }

    _st_ifnotst(pb_print_1(argc, median_loops, op1_str, op1_str_short))
    _st_store_1(median_runs, run, median_loops)
  }

  // all results must be within 'spec' at the same time
  // does not save 'best' results
  _st_check_1(sd_runs, mean_runs, median_runs)

_st_while_e

_st_print_1(argc, sd_runs, mean_runs, median_runs, op1_str, op1_str_short)

  free(_result);
  free(_base);
  free(_exp);
  free(_mod);

  return 0;
}

