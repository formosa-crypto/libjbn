#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <gmp.h>

#include "params.h"


void params_load(mpz_t dest, int dest_init, const uint64_t *src, size_t NLIMBS)
{
  if(dest_init == 1)
	{ mpz_init2(dest, NLIMBS*64); }

  mpz_import(dest, NLIMBS, -1, sizeof(uint64_t), 0, 0, src);
}


void params_load_from_string(uint64_t *_P, const char *str, size_t NLIMBS)
{
  int r;
  mpz_t P;

	mpz_init2(P, NLIMBS*64);
  r = mpz_set_str(P, str, 0); // base = 0 => 0x,0X:hex; 0b,0B:bin; 0:octal; otherwise:decimal;
  assert(r == 0);

  params_store(_P, NLIMBS, P, 1, "from_string");
}


void params_store(uint64_t *dest, size_t NLIMBS, mpz_t src, int src_clear, char *debug)
{
  uint64_t *r;
  size_t count = NLIMBS;
  size_t sizeinbase = mpz_sizeinbase(src,2);

  if(sizeinbase > NLIMBS*64)
  { gmp_fprintf(stderr, "error: %s : 0x%Zx = %zu bits\n", debug, src, sizeinbase);
    exit(-1); }

  memset(dest, 0, sizeof(uint64_t) * NLIMBS);
  r = mpz_export(dest, &count, -1, sizeof(uint64_t), 0, 0, src);

  assert( r == dest );
  assert( count <= NLIMBS);

  if(src_clear == 1)
  { mpz_clear(src); }
}


//
//
//


// R = 2^(NLIMBS*64)
void params_set_R(mpz_t R, size_t NLIMBS)
{
  mpz_init_set_ui(R, 1);
  mpz_mul_2exp(R, R, NLIMBS*64);
}


// R = 2^(NLIMBS*64); and also asserts that: gcd(R,P) == 1 && 2*P < R
void params_set_and_check_R(mpz_t R, const mpz_t P, size_t NLIMBS)
{
  mpz_t gcd, one, P2;

  // set R to 2**(NLIMBS*64)
  params_set_R(R, NLIMBS);

  // set: gcd to 0; one to 1; P to 2*P
  mpz_init_set_ui(gcd, 0);
  mpz_init_set_ui(one, 1);
  mpz_init_set(P2, P);
  mpz_mul_2exp(P2, P2, 1);

  // check if gcd(R,P) is different than one;
  // mpz_cmp: "returns a positive value if op1 > op2 ; zero if op1 = op2 ; negative value if op1 < op2"
  mpz_gcd(gcd, R, P);
  assert(mpz_cmp(gcd, one) == 0);
  assert(mpz_cmp(P2, R) < 0);

  // clear gcd and one
  mpz_clears(gcd, one, P2, NULL);
}


// Rmp = R - P == 2^(NLIMBS*64) - P
void params_precompute_RmP(uint64_t *_RmP, const uint64_t *_P, size_t NLIMBS)
{
  mpz_t RmP, R, P;

  // load P and set R
  params_load(P, 1, _P, NLIMBS);
  params_set_and_check_R(R, P, NLIMBS);

  // RmP = R - P
	mpz_init2(RmP, NLIMBS*64);
  mpz_sub(RmP, R, P);

  // store and free
  params_store(_RmP, NLIMBS, RmP, 1, "RmP");
  mpz_clears(R, P, NULL);
}


// Pm2 = P - 2
void params_precompute_Pm2(uint64_t *_Pm2, const uint64_t *_P, size_t NLIMBS)
{
  mpz_t Pm2, P, two;

  // load P, set two = 2, init Pm2
  params_load(P, 1, _P, NLIMBS);
  mpz_init_set_ui(two, 2);
	mpz_init2(Pm2, NLIMBS*64);

  // P - 2
  mpz_sub(Pm2, P, two);

  // store and free
  params_store(_Pm2, NLIMBS, Pm2, 1, "Pm2");
  mpz_clears(P, two, NULL);
}


// u0 : (P[0] * u0) mod 2^64 == -1
void params_precompute_u0(uint64_t *_u0, const uint64_t *_P)
{
  int r;
  mpz_t u0, p0, m;

  // u0 = 0; p0 = P[0]; m = 2**64;
  mpz_init_set_ui(u0, 0);
  mpz_init_set_ui(p0, _P[0]);
  mpz_init_set_ui(m, 1);
  mpz_mul_2exp(m, m, 64);

  //
  r = mpz_invert(u0, p0, m);
  assert(r != 0);

  mpz_mul_ui(u0, u0, 0xFFFFFFFFFFFFFFFF);
  mpz_mod(u0, u0, m);

  // store and free
  params_store(_u0, 1, u0, 1, "u0");
  mpz_clears(p0, m, NULL);
}


// R mod P = 2^(NLIMBS*64) mod P
void params_precompute_RmodP(uint64_t *_RmodP, const uint64_t *_P, size_t NLIMBS)
{
  mpz_t RmodP, R, P;

  // load P and set R
  params_load(P, 1, _P, NLIMBS);
  params_set_and_check_R(R, P, NLIMBS);

  // RmodP = R mod P
	mpz_init2(RmodP, NLIMBS*64);
  mpz_mod(RmodP, R, P);

  // store and free
  params_store(_RmodP, NLIMBS, RmodP, 1, "RmodP");
  mpz_clears(R, P, NULL);
}


// R^2 mod P = 2^(2*NLIMBS*64) mod P
void params_precompute_R2modP(uint64_t *_R2modP, const uint64_t *_P, size_t NLIMBS)
{
  mpz_t R2modP, R, P;

  // load P and set R
  params_load(P, 1, _P, NLIMBS);
  params_set_and_check_R(R, P, NLIMBS);

  // R2modP = R mod P
	mpz_init2(R2modP, (NLIMBS+1)*64);
  mpz_mul(R2modP, R, R);
  mpz_mod(R2modP, R2modP, P);

  // store and free
  params_store(_R2modP, NLIMBS, R2modP, 1, "R2modP");
  mpz_clears(R, P, NULL);
}


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
)
{
  if(dest_init == 1)
  {
    *P      = calloc(NLIMBS, sizeof(uint64_t));
    *RmP    = calloc(NLIMBS, sizeof(uint64_t));
    *Pm2    = calloc(NLIMBS, sizeof(uint64_t));
    *RmodP  = calloc(NLIMBS, sizeof(uint64_t));
    *R2modP = calloc(NLIMBS, sizeof(uint64_t));
  }

  // P
  params_load_from_string(*P, Pstr, NLIMBS);

  // RmP
  params_precompute_RmP(*RmP, *P, NLIMBS);

  // Pm2
  params_precompute_Pm2(*Pm2, *P, NLIMBS);

  // u0 : (glob_p[0] * u0) mod 2^64 == -1
  params_precompute_u0(u0, *P);

  // RmodP
  params_precompute_RmodP(*RmodP, *P, NLIMBS);

  // R2modP
  params_precompute_R2modP(*R2modP, *P, NLIMBS);
}


//
//
//


void params_fprintf(FILE *f, char *s1, uint64_t *src, size_t NLIMBS, char *s2)
{
  size_t i;

  assert(NLIMBS > 0);

  fprintf(f, "%s\n", s1);
  for(i = 0; i<(NLIMBS-1); i++)
  { printf("  0x%016" PRIx64 ",\n", src[i]); }
  printf("  0x%016" PRIx64 "\n", src[NLIMBS-1]);
  printf("%s\n\n", s2);
}


void params_print_jasmin(
  uint64_t *P,
  uint64_t *RmP,
  uint64_t *Pm2,
  uint64_t *RmodP,
  uint64_t *R2modP,
  uint64_t u0,
  size_t NLIMBS,
  FILE *fout
)
{
         fprintf(fout, "param int NLIMBS = %zu;\n\n", NLIMBS);

         fprintf(fout, "// glob_p = P\n");
  params_fprintf(fout, "u64[NLIMBS] glob_p = {", P, NLIMBS, "};");

         fprintf(fout, "// glob_mp = R - P == 2^(NLIMBS*64) - P\n");
  params_fprintf(fout, "u64[NLIMBS] glob_mp = {", RmP, NLIMBS, "};");

         fprintf(fout, "// glob_pm2 = P - 2\n");
  params_fprintf(fout, "u64[NLIMBS] glob_pm2 = {", Pm2, NLIMBS, "};");

         fprintf(fout, "// (glob_u0 * P[0]) mod 2^64 == -1\n");
         fprintf(fout, "u64 glob_u0 = 0x%" PRIx64 ";\n\n", u0);

         fprintf(fout, "// glob_oneM = R mod P == 2^(NLIMBS*64) mod P\n");
  params_fprintf(fout, "u64[NLIMBS] glob_oneM = {", RmodP, NLIMBS, "};");

         fprintf(fout, "// glob_rM = R^2 mod P == 2^(2*NLIMBS*64) mod P\n");
  params_fprintf(fout, "u64[NLIMBS] glob_rM = {", R2modP, NLIMBS, "};");

      fprintf(fout, "from Libjbn require \"common/fp/amd64/ref/fp_generic_export.jinc\"\n\n");
}


void params_print_c(
  uint64_t *P,
  uint64_t *RmP,
  uint64_t *Pm2,
  uint64_t *RmodP,
  uint64_t *R2modP,
  uint64_t u0,
  size_t NLIMBS,
  FILE *fout
)
{
         fprintf(fout, "#include <stdint.h>\n\n");

         fprintf(fout, "#define NLIMBS %zu\n\n", NLIMBS);

         fprintf(fout, "// glob_p = P\n");
  params_fprintf(fout, "uint64_t glob_p[NLIMBS] = {", P, NLIMBS, "};");

         fprintf(fout, "// glob_mp = R - P == 2^(NLIMBS*64) - P\n");
  params_fprintf(fout, "uint64_t glob_mp[NLIMBS] = {", RmP, NLIMBS, "};");

         fprintf(fout, "// glob_pm2 = P - 2\n");
  params_fprintf(fout, "uint64_t glob_pm2[NLIMBS] = {", Pm2, NLIMBS, "};");

         fprintf(fout, "// (glob_u0 * P[0]) mod 2^64 == -1\n");
         fprintf(fout, "uint64_t glob_u0 = 0x%" PRIx64 ";\n\n", u0);

         fprintf(fout, "// glob_oneM = R mod P == 2^(NLIMBS*64) mod P\n");
  params_fprintf(fout, "uint64_t glob_oneM[NLIMBS] = {", RmodP, NLIMBS, "};");

         fprintf(fout, "// glob_rM = R^2 mod P == 2^(2*NLIMBS*64) mod P\n");
  params_fprintf(fout, "uint64_t glob_rM[NLIMBS] = {", R2modP, NLIMBS, "};");
}


//


#ifdef _MAIN_PARAMS
int main(int argc, char **argv)
{
  size_t NLIMBS;
  uint64_t *P, *RmP, *Pm2, *RmodP, *R2modP;
  uint64_t u0;
  FILE *fout = stdout;

  // check argc and load NLIMBS
  if(argc != 4)
  { fprintf(stderr, "usage:   ./params (j||c) NLIMBS NUMBER\n");
    fprintf(stderr, "example: ./params j 7 0x0002341f271773446cfc5fd681c520567bc65c783158aea3fdc1767ae2ffffffffffffffffffffffffffffffffffffffffffffffffffffff\n");
    return -1;
  }

  NLIMBS = strtoull(argv[2], NULL, 0);
  assert(NLIMBS >= 1 && NLIMBS <= 256);

  // precompute and print
  params_precompute_all(&P, &RmP, &Pm2, &RmodP, &R2modP, &u0, 1, argv[3], NLIMBS);

  if(strcmp(argv[1], "j") == 0)
  { params_print_jasmin(P, RmP, Pm2, RmodP, R2modP, u0, NLIMBS, fout); }
  else
  { params_print_c(P, RmP, Pm2, RmodP, R2modP, u0, NLIMBS, fout); }

  // clear
  free(P     );
  free(RmP   );
  free(Pm2   );
  free(RmodP );
  free(R2modP);

  return 0;
}
#endif
