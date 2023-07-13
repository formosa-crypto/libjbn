#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <gmp.h>

#include "params.h"
#include "barrett.h"

void barrett_precompute(uint64_t *barrett_factor, uint64_t *mod, size_t NLIMBS)
{
  mpz_t m_barrett_factor, m_k, m_mod;
  size_t barrett_factor_count;

  //
  // m_barrett_factor = floor( 4**k / mod ); export barrett_factor to an array with 2*NLIMBS
  //

  // set m_k to 4**k
  mpz_init_set_ui(m_k, 1);
  mpz_mul_2exp(m_k, m_k, NLIMBS*64*2);

  // load m_mod
	mpz_init2(m_mod, NLIMBS*64);
  mpz_import(m_mod,  NLIMBS, -1, sizeof(uint64_t), 0, 0, mod);

  // init m_barrett
	mpz_init2(m_barrett_factor, NLIMBS*64*2);

  // r = floor( 4**k / mod )
  mpz_fdiv_q(m_barrett_factor, m_k, m_mod);

  // export barrett_factor
  memset(barrett_factor, 0, sizeof(uint64_t)*NLIMBS*2);
  mpz_export(barrett_factor, &barrett_factor_count, -1, sizeof(uint64_t), 0, 0, m_barrett_factor);

  assert(NLIMBS*2 >= barrett_factor_count);

  mpz_clears(m_barrett_factor, m_k, m_mod, NULL);
}


void barrett_print_jasmin(
  uint64_t *barrett_factor,
  size_t NLIMBS,
  FILE *fout
)
{
         fprintf(fout, "param int NLIMBS = %zu;\n\n", NLIMBS);
  params_fprintf(fout, "u64[NLIMBS*2] barrett_factor = {", barrett_factor, NLIMBS*2, "};");
}


void barrett_print_c(
  uint64_t *barrett_factor,
  size_t NLIMBS,
  FILE *fout
)
{
         fprintf(fout, "#include <stdint.h>\n\n");
         fprintf(fout, "#define NLIMBS %zu\n\n", NLIMBS);
  params_fprintf(fout, "uint64_t barrett_reduction[NLIMBS*2] = {", barrett_factor, NLIMBS*2, "};");
}


//


#ifdef _MAIN_BARRETT
int main(int argc, char **argv)
{
  size_t NLIMBS;
  uint64_t *barrett_factor, *mod;
  FILE *fout = stdout;

  // check argc and load NLIMBS
  if(argc != 4)
  { fprintf(stderr, "usage:   ./barrett (j||c) NLIMBS NUMBER\n");
    fprintf(stderr, "example: ./barrett j 7 0x0002341f271773446cfc5fd681c520567bc65c783158aea3fdc1767ae2ffffffffffffffffffffffffffffffffffffffffffffffffffffff\n");
    return -1;
  }

  NLIMBS = strtoull(argv[2], NULL, 0);
  assert(NLIMBS >= 1 && NLIMBS <= 256);

  // 
  barrett_factor = calloc(NLIMBS*2, sizeof(uint64_t));
  mod = calloc(NLIMBS, sizeof(uint64_t));

  //
  params_load_from_string(mod, argv[3], NLIMBS);
  barrett_precompute(barrett_factor, mod, NLIMBS);

  // 
  if(strcmp(argv[1], "j") == 0)
  { barrett_print_jasmin(barrett_factor, NLIMBS, fout); }
  else
  { barrett_print_c(barrett_factor, NLIMBS, fout); }

  // clear
  free(barrett_factor);
  free(mod);

  return 0;
}
#endif


