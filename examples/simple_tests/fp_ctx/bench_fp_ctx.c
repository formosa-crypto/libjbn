/* Timing of fpc_mul, fpc_sqr and fpc_exp for one field instance (best of a
   few runs, wall-clock time): see the `bench` target of the Makefile, which
   builds this program for each size and each multiplication module
   (bn_mul and bn_mulx, unrolled; bn_mul_loop and bn_mulx_loop, looping over
   the rows; bn_mulxr, with the accumulator in registers), and for the
   pseudo-Mersenne field (fp_pm).

   Build with -DNLIMBS=<n> -DVARIANT=\"<name>\", and -DPM for an fp_pm
   instance: the modulus is then 2^(64 NLIMBS - 1) - 19 (2^255-19 at 4
   limbs; R mod P = 38), instead of a random one, which fp_pm does not
   take. */
#include <stdint.h>
#include <stdio.h>
#include <time.h>

#ifndef NLIMBS
#error "NLIMBS"
#endif
#ifndef VARIANT
#define VARIANT "?"
#endif
#define CTXLEN (4 * NLIMBS + 1)

extern void fpc_ctx_init(uint64_t *ctx, const uint64_t *p);
extern void fpc_mul(uint64_t *r, const uint64_t *a, const uint64_t *b, const uint64_t *ctx);
extern void fpc_sqr(uint64_t *r, const uint64_t *a, const uint64_t *ctx);
extern void fpc_exp(uint64_t *r, const uint64_t *a, const uint64_t *b, const uint64_t *ctx);

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1e9 + t.tv_nsec;
}

/* xorshift64 */
static uint64_t s = 88172645463325252ULL;
static uint64_t rng(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }

int main(void) {
  uint64_t P[NLIMBS], ctx[CTXLEN], a[NLIMBS], b[NLIMBS], e[NLIMBS], r[NLIMBS];
  double best_m = 1e30, best_s = 1e30, best_e = 1e30, t;
  long reps, ereps, i;
  int k;

  /* a full-size odd modulus, operands below it, a full-size exponent */
  for (k = 0; k < NLIMBS; k++) { P[k] = rng(); a[k] = rng(); b[k] = rng(); e[k] = rng(); }
#ifdef PM
  for (k = 0; k < NLIMBS; k++) P[k] = ~(uint64_t) 0;
  P[NLIMBS - 1] >>= 1;
  P[0] -= 18;
#else
  P[0] |= 1;
  P[NLIMBS - 1] |= (uint64_t) 1 << 63;
#endif
  a[NLIMBS - 1] >>= 2;
  b[NLIMBS - 1] >>= 2;
  fpc_ctx_init(ctx, P);

  reps = 40000000L / (NLIMBS * NLIMBS + 40);
  for (k = 0; k < 7; k++) {
    t = now(); for (i = 0; i < reps; i++) fpc_mul(r, a, b, ctx);
    t = (now() - t) / reps; if (t < best_m) best_m = t;
    t = now(); for (i = 0; i < reps; i++) fpc_sqr(r, a, ctx);
    t = (now() - t) / reps; if (t < best_s) best_s = t;
  }
  ereps = reps / (128 * NLIMBS) + 1;
  for (k = 0; k < 3; k++) {
    t = now(); for (i = 0; i < ereps; i++) fpc_exp(r, a, e, ctx);
    t = (now() - t) / ereps; if (t < best_e) best_e = t;
  }
  printf("%-8s n=%-3d fpc_mul %9.1f ns  fpc_sqr %9.1f ns  fpc_exp %12.1f us\n",
         VARIANT, NLIMBS, best_m, best_s, best_e / 1e3);
  return 0;
}
