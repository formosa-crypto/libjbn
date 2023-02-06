#ifndef TEST_MISC_GEN
#define TEST_MISC_GEN

#include <stdint.h>
#include <gmp.h>

void gen_load(mpz_t dest, int dest_init, const uint64_t *src, size_t NLIMBS);

void gen_store(uint64_t *dest, size_t NLIMBS, mpz_t src, int src_clear);

void gen_set_and_check_R(mpz_t R, const mpz_t P, size_t NLIMBS);

//

void gen_precompute_RmP(uint64_t *_RmP, const uint64_t *_P, size_t NLIMBS);

void gen_precompute_Pm2(uint64_t *_Pm2, const uint64_t *_P, size_t NLIMBS);

void gen_precompute_u0(uint64_t *_u0, const uint64_t *_P);

void gen_precompute_RmodP(uint64_t *_RmodP, const uint64_t *_P, size_t NLIMBS);

void gen_precompute_R2modP(uint64_t *_R2modP, const uint64_t *_P, size_t NLIMBS);

void gen_precompute_all(
  uint64_t **P,
  uint64_t **RmP,
  uint64_t **Pm2,
  uint64_t **RmodP,
  uint64_t **R2modP,
  uint64_t *u0,

  int dest_init,
  char *Pstr,
  size_t NLIMBS
);

//

void gen_load_from_string(uint64_t *_P, const char *str, size_t NLIMBS);

void gen_fprintf(FILE *f, char *s1, uint64_t *src, size_t NLIMBS, char *s2);

void gen_print_jasmin(
  uint64_t *P,
  uint64_t *RmP,
  uint64_t *Pm2,
  uint64_t *RmodP,
  uint64_t *R2modP,
  uint64_t u0,
  size_t NLIMBS,
  FILE *fout
);

void gen_print_c(
  uint64_t *P,
  uint64_t *RmP,
  uint64_t *Pm2,
  uint64_t *RmodP,
  uint64_t *R2modP,
  uint64_t u0,
  size_t NLIMBS,
  FILE *fout
);

#endif
