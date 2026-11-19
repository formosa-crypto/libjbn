/* Tests of the fpc_* entry points (run-time moduli), against the vectors
   of gen_vectors.py: the context computed by fpc_ctx_init, and each
   operation with that context. */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#ifndef NLIMBS
#error "NLIMBS"
#endif
#define CTXLEN (4 * NLIMBS + 1)

extern void fpc_ctx_init(uint64_t *ctx, const uint64_t *p);
extern void fpc_add(uint64_t *r, const uint64_t *a, const uint64_t *b, const uint64_t *ctx);
extern void fpc_sub(uint64_t *r, const uint64_t *a, const uint64_t *b, const uint64_t *ctx);
extern void fpc_mul(uint64_t *r, const uint64_t *a, const uint64_t *b, const uint64_t *ctx);
extern void fpc_sqr(uint64_t *r, const uint64_t *a, const uint64_t *ctx);
extern void fpc_toM(uint64_t *r, const uint64_t *a, const uint64_t *ctx);
extern void fpc_fromM(uint64_t *r, const uint64_t *a, const uint64_t *ctx);
extern void fpc_exp(uint64_t *r, const uint64_t *a, const uint64_t *b, const uint64_t *ctx);
extern void fpc_exp_noct(uint64_t *r, const uint64_t *a, const uint64_t *b, const uint64_t *ctx);
extern void fpc_inv(uint64_t *r, const uint64_t *a, const uint64_t *ctx);

static void rd(uint64_t *x, int n) {
  for (int i = 0; i < n; i++)
    if (scanf("%" SCNx64, &x[i]) != 1) { fprintf(stderr, "bad input\n"); }
}

static int bad = 0, checks = 0;
static void check(const char *what, int m, const uint64_t *got, const uint64_t *want, int n) {
  checks++;
  if (memcmp(got, want, 8 * n)) {
    if (bad++ < 10) printf("modulus %d: %s wrong\n", m, what);
  }
}

int main(void) {
  int nm;
  if (scanf("%d", &nm) != 1) return 2;
  for (int m = 0; m < nm; m++) {
    uint64_t P[NLIMBS], want_ctx[CTXLEN], ctx[CTXLEN];
    int ncases, prime;
    rd(P, NLIMBS); rd(want_ctx, CTXLEN);
    if (scanf("%d %d", &ncases, &prime) != 2) return 2;
    fpc_ctx_init(ctx, P);
    check("ctx", m, ctx, want_ctx, CTXLEN);
    for (int c = 0; c < ncases; c++) {
      uint64_t a[NLIMBS], b[NLIMBS], e[NLIMBS], want[8][NLIMBS], r[NLIMBS];
      rd(a, NLIMBS); rd(b, NLIMBS); rd(e, NLIMBS);
      for (int k = 0; k < 8; k++) rd(want[k], NLIMBS);
      fpc_add(r, a, b, ctx);      check("add", m, r, want[0], NLIMBS);
      fpc_sub(r, a, b, ctx);      check("sub", m, r, want[1], NLIMBS);
      fpc_mul(r, a, b, ctx);      check("mul", m, r, want[2], NLIMBS);
      fpc_sqr(r, a, ctx);         check("sqr", m, r, want[3], NLIMBS);
      fpc_toM(r, a, ctx);         check("toM", m, r, want[4], NLIMBS);
      fpc_fromM(r, a, ctx);       check("fromM", m, r, want[5], NLIMBS);
      fpc_exp(r, a, e, ctx);      check("exp", m, r, want[6], NLIMBS);
      fpc_exp_noct(r, a, e, ctx); check("exp_noct", m, r, want[6], NLIMBS);
      if (prime) { fpc_inv(r, a, ctx); check("inv", m, r, want[7], NLIMBS); }
    }
  }
  printf("NLIMBS=%d: %d moduli, %d checks, %d wrong\n", NLIMBS, nm, checks, bad);
  return bad != 0;
}
