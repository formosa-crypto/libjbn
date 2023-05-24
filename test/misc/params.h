#ifndef TEST_MISC_PARAMS
#define TEST_MISC_PARAMS

#include <stdint.h>
#include <gmp.h>

void params_load(mpz_t dest, int dest_init, const uint64_t *src, size_t NLIMBS);

void params_store(uint64_t *dest, size_t NLIMBS, mpz_t src, int src_clear, char *debug);

//

void params_set_R(mpz_t R, size_t NLIMBS);

void params_set_and_check_R(mpz_t R, const mpz_t P, size_t NLIMBS);

//

void params_precompute_RmP(uint64_t *_RmP, const uint64_t *_P, size_t NLIMBS);

void params_precompute_Pm2(uint64_t *_Pm2, const uint64_t *_P, size_t NLIMBS);

void params_precompute_u0(uint64_t *_u0, const uint64_t *_P);

void params_precompute_RmodP(uint64_t *_RmodP, const uint64_t *_P, size_t NLIMBS);

void params_precompute_R2modP(uint64_t *_R2modP, const uint64_t *_P, size_t NLIMBS);

void params_precompute_all(
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

void params_load_from_string(uint64_t *_P, const char *str, size_t NLIMBS);

void params_fprintf(FILE *f, char *s1, uint64_t *src, size_t NLIMBS, char *s2);

void params_print_jasmin(
  uint64_t *P,
  uint64_t *RmP,
  uint64_t *Pm2,
  uint64_t *RmodP,
  uint64_t *R2modP,
  uint64_t u0,
  size_t NLIMBS,
  FILE *fout
);

void params_print_c(
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
