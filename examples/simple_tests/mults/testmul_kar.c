/* Test of the Karatsuba multiplication (bn_karatsuba, one or more levels),
   against a schoolbook reference in C.

   Build with -DNLIMBS=<n> (operand size, in limbs; even) and link with a
   Karatsuba instance of that size (kar_<n>_*.s).

   With a = alo + B * ahi and b = blo + B * bhi, the routine multiplies
   |alo - ahi| by |bhi - blo| and negates the product when the signs differ:
   besides constant, edge-case and random operands, the tests take each
   difference zero, positive, negative and one apart (with and without a
   carry through the half), in every combination. A zero difference with
   the other one negative is the case in which the top word was wrong
   (a = 0, b = 1). */
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#ifndef NLIMBS
#define NLIMBS 32
#endif
#define HLIMBS (NLIMBS / 2)

extern void bn_kar_muln(uint64_t*, const uint64_t*, const uint64_t*);

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

/* y, a half at a given distance of x:
     0: y = x       1: y = x + 1       2: y = x - 1
     3: y = x + 1, x ending with a run of all-ones limbs (a carry)
     4: y = x - 1, x ending with a run of zero limbs (a borrow)
     5: y random    6: y = x but for one limb */
#define NKINDS 7
static void half_near(uint64_t y[], uint64_t x[], int kind) {
  int j, k;
  switch (kind) {
    case 3:
      k = (int) (rng() % (HLIMBS + 1));
      for (j = 0; j < k; j++) x[j] = ~(uint64_t) 0;
      break;
    case 4:
      k = (int) (rng() % (HLIMBS + 1));
      for (j = 0; j < k; j++) x[j] = 0;
      break;
  }
  memcpy(y, x, HLIMBS * sizeof(uint64_t));
  switch (kind) {
    case 1: case 3: half_inc(y); break;
    case 2: case 4: half_dec(y); break;
    case 5: half_rnd(y); break;
    case 6: y[rng() % HLIMBS] = rng(); break;
  }
}

static int errors = 0, tests = 0;

static void check(const char *what, const uint64_t alo[], const uint64_t ahi[],
                  const uint64_t blo[], const uint64_t bhi[]) {
  uint64_t a[NLIMBS], b[NLIMBS], expected[2 * NLIMBS], got[2 * NLIMBS];
  memcpy(a, alo, HLIMBS * sizeof(uint64_t));
  memcpy(a + HLIMBS, ahi, HLIMBS * sizeof(uint64_t));
  memcpy(b, blo, HLIMBS * sizeof(uint64_t));
  memcpy(b + HLIMBS, bhi, HLIMBS * sizeof(uint64_t));
  ref_mul(expected, a, b);
  memset(got, 0xa5, sizeof got);
  bn_kar_muln(got, a, b);
  tests++;
  if (memcmp(expected, got, sizeof got) != 0) {
    if (errors < 10) printf("FAIL mul (%s)\n", what);
    errors++;
  }
}

int main(void) {
  uint64_t alo[HLIMBS], ahi[HLIMBS], blo[HLIMBS], bhi[HLIMBS];
  uint64_t csts[] = { 0, 1, ~(uint64_t) 0, (uint64_t) 1 << 63 };
  long i;
  int j, k, l, m;

  /* constant halves: every combination (a = 0 and b = 1 among them) */
  for (j = 0; j < 4; j++) for (k = 0; k < 4; k++) for (l = 0; l < 4; l++) for (m = 0; m < 4; m++) {
    half_cst(alo, csts[j]); half_cst(ahi, csts[k]);
    half_cst(blo, csts[l]); half_cst(bhi, csts[m]);
    check("constant halves", alo, ahi, blo, bhi);
  }
  /* small operands: a and b of one limb, in each half */
  for (i = 0; i < 2000; i++) {
    half_cst(alo, 0); half_cst(ahi, 0); half_cst(blo, 0); half_cst(bhi, 0);
    alo[0] = rng() % 3; ahi[0] = rng() % 3; blo[0] = rng() % 3; bhi[0] = rng() % 3;
    check("small", alo, ahi, blo, bhi);
  }
  /* each pair of halves at each distance, in every combination: both
     signs of both differences, and zero differences */
  for (i = 0; i < 400; i++)
    for (j = 0; j < NKINDS; j++) for (k = 0; k < NKINDS; k++) {
      if (i & 1) half_rnd(ahi); else half_edge(ahi);
      half_near(alo, ahi, j);
      if (i & 2) half_rnd(blo); else half_edge(blo);
      half_near(bhi, blo, k);
      check("halves at a distance", alo, ahi, blo, bhi);
      check("halves at a distance (a swapped)", ahi, alo, blo, bhi);
      check("halves at a distance (b swapped)", alo, ahi, bhi, blo);
      check("halves at a distance (both swapped)", ahi, alo, bhi, blo);
    }
  /* edge-case and random limbs */
  for (i = 0; i < 20000; i++) {
    half_edge(alo); half_edge(ahi); half_edge(blo); half_edge(bhi);
    check("edge", alo, ahi, blo, bhi);
    half_rnd(alo); half_rnd(ahi); half_rnd(blo); half_rnd(bhi);
    check("random", alo, ahi, blo, bhi);
  }
  printf("TESTING mul_kar, %d limbs: %d tests, %d errors\n", NLIMBS, tests, errors);
  if (errors) return 1;
  printf("...OK!\n");
  return 0;
}
