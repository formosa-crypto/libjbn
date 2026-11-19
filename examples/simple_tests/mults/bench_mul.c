/* Timing of one multiplication entry point and, optionally, of one squaring
   entry point (best of a few runs, wall-clock time): see the `bench` and
   `bench-kar` targets of the Makefile, which build this program for each
   size and each routine.

   Build with -DNLIMBS=<n> -DFN=<multiplication> [-DFN_SQR=<squaring>]
   -DVARIANT=\"<name>\". The entry points copy their operands in and the
   product out (6*n words; 5*n for a squaring), which is the same code for
   every variant. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#ifndef NLIMBS
#error "NLIMBS"
#endif
#ifndef FN
#error "FN"
#endif
#ifndef VARIANT
#define VARIANT "?"
#endif

extern void FN(uint64_t *r, const uint64_t *a, const uint64_t *b);
#ifdef FN_SQR
extern void FN_SQR(uint64_t *r, const uint64_t *a);
#endif

/* reference: r[0..2n-1] = a * b */
static void ref_mul(uint64_t r[], const uint64_t a[], const uint64_t b[]) {
  int i, j;
  memset(r, 0, 2 * NLIMBS * sizeof(uint64_t));
  for (i = 0; i < NLIMBS; i++) {
    uint64_t carry = 0;
    for (j = 0; j < NLIMBS; j++) {
      unsigned __int128 t = (unsigned __int128) a[i] * b[j] + r[i + j] + carry;
      r[i + j] = (uint64_t) t;
      carry = (uint64_t) (t >> 64);
    }
    r[i + NLIMBS] = carry;
  }
}

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1e9 + t.tv_nsec;
}

/* xorshift64 */
static uint64_t s = 88172645463325252ULL;
static uint64_t rng(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }

int main(void) {
  uint64_t a[NLIMBS], b[NLIMBS], r[2 * NLIMBS], e[2 * NLIMBS];
  double best = 1e30, t;
  long reps, i;
  int k;

  for (k = 0; k < NLIMBS; k++) { a[k] = rng(); b[k] = rng(); }

  reps = 40000000L / (NLIMBS * NLIMBS + 40);
  for (k = 0; k < 9; k++) {
    t = now(); for (i = 0; i < reps; i++) FN(r, a, b);
    t = (now() - t) / reps; if (t < best) best = t;
  }
  ref_mul(e, a, b);
  if (memcmp(r, e, sizeof r) != 0) { printf("%s n=%d: WRONG PRODUCT\n", VARIANT, NLIMBS); return 1; }
  printf("%-13s n=%-3d mul %9.1f ns  (%.3f ns per limb product)",
         VARIANT, NLIMBS, best, best / (NLIMBS * NLIMBS));
#ifdef FN_SQR
  best = 1e30;
  for (k = 0; k < 9; k++) {
    t = now(); for (i = 0; i < reps; i++) FN_SQR(r, a);
    t = (now() - t) / reps; if (t < best) best = t;
  }
  ref_mul(e, a, a);
  if (memcmp(r, e, sizeof r) != 0) { printf("\n%s n=%d: WRONG SQUARE\n", VARIANT, NLIMBS); return 1; }
  printf("   sqr %9.1f ns", best);
#endif
  printf("\n");
  return 0;
}
