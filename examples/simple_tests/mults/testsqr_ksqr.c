/* Test of the squaring over the half size (bn_ksqr), against a schoolbook
   reference in C.

   Build with -DNLIMBS=<n> (operand size, in limbs; even) and link with the
   matching instance (sqrn<n>_ksqr.s, sqrn<n>_ksqr2.s).

   With a = lo + B * hi, the routine squares lo, hi and |lo - hi|, and
   counts the borrows of three subtractions: besides constant, edge-case
   and random operands, the tests take lo = hi, lo = hi +- 1 (with and
   without a carry through the half), lo < hi and lo > hi differing in one
   limb, and a zero or an all-ones half. */
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#ifndef NLIMBS
#define NLIMBS 32
#endif
#define HLIMBS (NLIMBS / 2)

extern void bn_kar_sqrn(uint64_t*, const uint64_t*);

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

/* halves (HLIMBS words) */
static void half_rnd(uint64_t x[]) { int i; for (i = 0; i < HLIMBS; i++) x[i] = rng(); }
static void half_cst(uint64_t x[], uint64_t c) { int i; for (i = 0; i < HLIMBS; i++) x[i] = c; }
/* limbs taken among 0, 1, 2^64-1, 2^63 and random ones */
static void half_edge(uint64_t x[]) {
  int i;
  for (i = 0; i < HLIMBS; i++) {
    switch (rng() % 5) {
      case 0: x[i] = 0; break;
      case 1: x[i] = 1; break;
      case 2: x[i] = ~(uint64_t) 0; break;
      case 3: x[i] = (uint64_t) 1 << 63; break;
      default: x[i] = rng();
    }
  }
}
/* x += 1, x -= 1 (modulo B) */
static void half_inc(uint64_t x[]) { int i; for (i = 0; i < HLIMBS; i++) if (++x[i] != 0) break; }
static void half_dec(uint64_t x[]) { int i; for (i = 0; i < HLIMBS; i++) if (x[i]-- != 0) break; }

static int errors = 0, tests = 0;

static void check(const char *what, const uint64_t lo[], const uint64_t hi[]) {
  uint64_t a[NLIMBS], expected[2 * NLIMBS], got[2 * NLIMBS];
  memcpy(a, lo, HLIMBS * sizeof(uint64_t));
  memcpy(a + HLIMBS, hi, HLIMBS * sizeof(uint64_t));
  ref_mul(expected, a, a);
  memset(got, 0x5a, sizeof got);
  bn_kar_sqrn(got, a);
  tests++;
  if (memcmp(expected, got, sizeof got) != 0) {
    if (errors < 10) printf("FAIL sqr (%s)\n", what);
    errors++;
  }
}

int main(void) {
  uint64_t lo[HLIMBS], hi[HLIMBS];
  uint64_t csts[] = { 0, 1, ~(uint64_t) 0, (uint64_t) 1 << 63 };
  long i;
  int j, k;

  /* constant halves: a = 0, all ones, lo = hi, a zero half, an all-ones half */
  for (j = 0; j < 4; j++) for (k = 0; k < 4; k++) {
    half_cst(lo, csts[j]); half_cst(hi, csts[k]);
    check("constant halves", lo, hi);
  }
  /* a zero half or an all-ones half, the other random or edge */
  for (i = 0; i < 2000; i++) {
    half_rnd(lo); half_cst(hi, 0);               check("hi = 0", lo, hi);
    half_cst(lo, 0); half_rnd(hi);               check("lo = 0", lo, hi);
    half_edge(lo); half_cst(hi, ~(uint64_t) 0);  check("hi = B-1", lo, hi);
    half_cst(lo, ~(uint64_t) 0); half_edge(hi);  check("lo = B-1", lo, hi);
  }
  /* lo = hi, lo = hi + 1, lo = hi - 1; with a run of all-ones (of zero)
     low limbs, the increment (decrement) carries through them */
  for (i = 0; i < 20000; i++) {
    if (i & 1) half_rnd(hi); else half_edge(hi);
    memcpy(lo, hi, sizeof lo);                   check("lo = hi", lo, hi);
    half_inc(lo);                                check("lo = hi + 1", lo, hi);
    memcpy(lo, hi, sizeof lo); half_dec(lo);     check("lo = hi - 1", lo, hi);
    k = (int) (rng() % (HLIMBS + 1));
    for (j = 0; j < k; j++) hi[j] = ~(uint64_t) 0;
    memcpy(lo, hi, sizeof lo); half_inc(lo);     check("lo = hi + 1, carry", lo, hi);
    for (j = 0; j < k; j++) hi[j] = 0;
    memcpy(lo, hi, sizeof lo); half_dec(lo);     check("lo = hi - 1, borrow", lo, hi);
  }
  /* halves that differ in one limb: lo < hi and lo > hi */
  for (i = 0; i < 20000; i++) {
    half_rnd(hi); memcpy(lo, hi, sizeof lo);
    k = (int) (rng() % HLIMBS);
    lo[k] ^= (uint64_t) 1 << (rng() % 64);
    check("one bit apart", lo, hi);
    lo[k] = rng();
    check("one limb apart", lo, hi);
  }
  /* edge-case and random limbs */
  for (i = 0; i < 20000; i++) {
    half_edge(lo); half_edge(hi); check("edge", lo, hi);
    half_rnd(lo); half_rnd(hi);   check("random", lo, hi);
    half_edge(lo); half_rnd(hi);  check("edge, random", lo, hi);
  }
  printf("TESTING sqr_ksqr, %d limbs: %d tests, %d errors\n", NLIMBS, tests, errors);
  if (errors) return 1;
  printf("...OK!\n");
  return 0;
}
