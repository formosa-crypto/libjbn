/* Timing of GMP's modular exponentiations, as a reference for fpc_exp
   (bench_fp_ctx.c): see the `bench-gmp` target of the Makefile. For each
   size given on the command line (in 64-bit limbs), with the operands of
   bench_fp_ctx.c (same generator and seed: a full-size odd modulus with its
   top bit set, a base below it, a full-size exponent), best of a few runs,
   wall-clock time:

     sec_mul   mpn_sec_mul, the product alone (n x n limbs, schoolbook): the
     sec_sqr   multiplication and squaring kernels of the exponentiation
               below, without the Montgomery reduction (mpn_sec_sqr)
     powm_sec  mpz_powm_sec, the side-channel silent exponentiation
     sec_powm  mpn_sec_powm, its core, on scratch space of the caller
     powm      mpz_powm, the fastest one (not constant time)

   An exponentiation of GMP includes what libjbn keeps in the context of the
   modulus or leaves to the caller: the conversions to and from Montgomery
   form, the inverse of the modulus modulo 2^64, and (per call, by its
   algorithm) the table of powers of the base. "window" is the window size
   of mpn_sec_powm for this exponent size, recovered from the scratch space
   it asks for (GMP 6: n * 2^window + 4n limbs); 0 if that fails.

   Stand-alone: cc -O2 -o bench_gmp bench_gmp.c -lgmp; ./bench_gmp 4 8 16 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <gmp.h>

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1e9 + t.tv_nsec;
}

/* xorshift64, as in bench_fp_ctx.c */
static uint64_t s;
static uint64_t rng(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }

static int window(mp_size_t n) {
  mp_size_t itch = mpn_sec_powm_itch(n, (mp_bitcnt_t) 64 * n, n), t;
  int w = 0;
  if (itch <= 8 * n + 2 || (itch - 4 * n) % n != 0) return 0;
  for (t = (itch - 4 * n) / n; t > 1; t >>= 1) { if (t & 1) return 0; w++; }
  return w;
}

static mp_limb_t *limbs(mp_size_t n) {
  mp_limb_t *p = malloc(n * sizeof(mp_limb_t));
  if (p == NULL) { fprintf(stderr, "out of memory\n"); exit(1); }
  return p;
}

static void bench(int n) {
  mp_limb_t *P = limbs(n), *a = limbs(n), *b = limbs(n), *e = limbs(n);
  mp_limb_t *r = limbs(n), *pr = limbs(2 * n);
  mp_limb_t *tm = limbs(mpn_sec_mul_itch(n, n) + 1), *ts = limbs(mpn_sec_sqr_itch(n) + 1);
  mp_limb_t *tp = limbs(mpn_sec_powm_itch(n, (mp_bitcnt_t) 64 * n, n));
  double best_m = 1e30, best_s = 1e30, best_zs = 1e30, best_ns = 1e30, best_z = 1e30, t;
  mpz_t zP, za, ze, zr, zq;
  long reps, ereps, i;
  int k, ok;

  /* the operands of bench_fp_ctx.c (b is the second factor of fpc_mul) */
  s = 88172645463325252ULL;
  for (k = 0; k < n; k++) { P[k] = rng(); a[k] = rng(); b[k] = rng(); e[k] = rng(); }
  P[0] |= 1;
  P[n - 1] |= (mp_limb_t) 1 << 63;
  a[n - 1] >>= 2;
  b[n - 1] >>= 2;
  mpz_inits(zP, za, ze, zr, zq, NULL);
  mpz_import(zP, n, -1, sizeof(mp_limb_t), 0, 0, P);
  mpz_import(za, n, -1, sizeof(mp_limb_t), 0, 0, a);
  mpz_import(ze, n, -1, sizeof(mp_limb_t), 0, 0, e);

  reps = 40000000L / ((long) n * n + 40);
  for (k = 0; k < 7; k++) {
    t = now(); for (i = 0; i < reps; i++) mpn_sec_mul(pr, a, n, b, n, tm);
    t = (now() - t) / reps; if (t < best_m) best_m = t;
    t = now(); for (i = 0; i < reps; i++) mpn_sec_sqr(pr, a, n, ts);
    t = (now() - t) / reps; if (t < best_s) best_s = t;
  }
  ereps = reps / (128 * n) + 1;
  for (k = 0; k < 3; k++) {
    t = now(); for (i = 0; i < ereps; i++) mpz_powm_sec(zr, za, ze, zP);
    t = (now() - t) / ereps; if (t < best_zs) best_zs = t;
    t = now(); for (i = 0; i < ereps; i++) mpn_sec_powm(r, a, n, e, (mp_bitcnt_t) 64 * n, P, n, tp);
    t = (now() - t) / ereps; if (t < best_ns) best_ns = t;
    t = now(); for (i = 0; i < ereps; i++) mpz_powm(zq, za, ze, zP);
    t = (now() - t) / ereps; if (t < best_z) best_z = t;
  }
  /* the three exponentiations agree */
  mpz_import(zP, n, -1, sizeof(mp_limb_t), 0, 0, r);   /* zP reused: the mpn result */
  ok = mpz_cmp(zr, zq) == 0 && mpz_cmp(zr, zP) == 0;

  printf("gmp      n=%-3d sec_mul %9.1f ns  sec_sqr %9.1f ns  powm_sec %11.1f us  "
         "sec_powm %11.1f us  powm %11.1f us  (window %d)%s\n",
         n, best_m, best_s, best_zs / 1e3, best_ns / 1e3, best_z / 1e3, window(n),
         ok ? "" : "  RESULTS DIFFER");
  mpz_clears(zP, za, ze, zr, zq, NULL);
  free(P); free(a); free(b); free(e); free(r); free(pr); free(tm); free(ts); free(tp);
}

int main(int argc, char **argv) {
  int i, n;
  if (sizeof(mp_limb_t) != 8 || mp_bits_per_limb != 64) {
    fprintf(stderr, "bench_gmp: needs a GMP with 64-bit limbs\n");
    return 1;
  }
  if (argc < 2) {
    fprintf(stderr, "usage: %s NLIMBS...\n", argv[0]);
    return 1;
  }
  printf("GMP %s\n", gmp_version);
  for (i = 1; i < argc; i++) {
    n = atoi(argv[i]);
    if (n < 1 || n > 4096) { fprintf(stderr, "bench_gmp: bad size %s\n", argv[i]); return 1; }
    bench(n);
  }
  return 0;
}
