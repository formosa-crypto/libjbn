/* Test of the row-looped operand-scanning multiplication and squaring
   (bn_mul_loop), against a schoolbook reference in C.

   Build with -DNLIMBS=<n> (operand size, in limbs) and link with the
   matching instance (muln<n>_loop.s). */
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#ifndef NLIMBS
#define NLIMBS 32
#endif

extern void bn_os_muln(uint64_t*, const uint64_t*, const uint64_t*);
extern void bn_os_sqrn(uint64_t*, const uint64_t*);

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

/* xorshift64* */
static uint64_t rng_state = 0x9e3779b97f4a7c15ULL;
static uint64_t rng(void) {
  rng_state ^= rng_state >> 12;
  rng_state ^= rng_state << 25;
  rng_state ^= rng_state >> 27;
  return rng_state * 0x2545f4914f6cdd1dULL;
}

static void fill_rnd(uint64_t x[])  { int i; for (i = 0; i < NLIMBS; i++) x[i] = rng(); }
static void fill_cst(uint64_t x[], uint64_t c) { int i; for (i = 0; i < NLIMBS; i++) x[i] = c; }
/* limbs taken among 0, 1, 2^64-1, 2^63 and random ones */
static void fill_edge(uint64_t x[]) {
  int i;
  for (i = 0; i < NLIMBS; i++) {
    switch (rng() % 5) {
      case 0: x[i] = 0; break;
      case 1: x[i] = 1; break;
      case 2: x[i] = ~(uint64_t) 0; break;
      case 3: x[i] = (uint64_t) 1 << 63; break;
      default: x[i] = rng();
    }
  }
}

static int errors = 0;

static void check(const char *what, const uint64_t a[], const uint64_t b[]) {
  uint64_t expected[2 * NLIMBS], got[2 * NLIMBS];
  ref_mul(expected, a, b);
  memset(got, 0xa5, sizeof got);
  bn_os_muln(got, a, b);
  if (memcmp(expected, got, sizeof got) != 0) {
    if (errors < 5) printf("FAIL mul (%s)\n", what);
    errors++;
  }
  if (a == b) {
    memset(got, 0x5a, sizeof got);
    bn_os_sqrn(got, a);
    if (memcmp(expected, got, sizeof got) != 0) {
      if (errors < 5) printf("FAIL sqr (%s)\n", what);
      errors++;
    }
  }
}

int main(int argc, char *argv[]) {
  uint64_t a[NLIMBS], b[NLIMBS], x[2 * NLIMBS], y[2 * NLIMBS];
  long i, reps = 10000000;
  int tests = 0;

  /* constant operands */
  uint64_t csts[] = { 0, 1, ~(uint64_t) 0, (uint64_t) 1 << 63 };
  for (i = 0; i < 4; i++) {
    int j;
    for (j = 0; j < 4; j++) {
      fill_cst(a, csts[i]); fill_cst(b, csts[j]);
      check("constant", a, b); tests++;
    }
    check("constant, square", a, a); tests++;
  }
  /* edge-case and random limbs */
  for (i = 0; i < 20000; i++) {
    fill_edge(a); fill_edge(b);
    check("edge", a, b); check("edge, square", a, a); tests += 2;
    fill_rnd(a); fill_rnd(b);
    check("random", a, b); check("random, square", a, a); tests += 2;
  }
  printf("TESTING mul_os_loop, %d limbs: %d tests, %d errors\n",
         NLIMBS, tests, errors);
  if (errors) return 1;

  /* timing loop (see the `run` target) */
  if (argc > 1) reps = 0;
  fill_rnd(a);
  for (i = 0; i < reps; i++) bn_os_muln(x, a, a);
  if (reps) {
    ref_mul(y, a, a);
    if (memcmp(x, y, sizeof x) != 0) { printf("FAIL after the timing loop\n"); return 1; }
  }
  printf("...OK!\n");
  return 0;
}
