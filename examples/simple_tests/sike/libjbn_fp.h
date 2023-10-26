#include <stdint.h>
extern uint64_t bn(uint64_t*, uint64_t*);
extern void bn_copy(uint64_t*, uint64_t*);
extern uint64_t bn_eq(uint64_t*, uint64_t*);
extern uint64_t bn_set0(uint64_t*, uint64_t*);
extern uint64_t bn_test0(uint64_t*, uint64_t*);

extern void fp_add(uint64_t*, uint64_t*, uint64_t*);
extern uint64_t fp_sub(uint64_t*, uint64_t*, uint64_t*);
extern uint64_t fp_mul(uint64_t*, uint64_t*, uint64_t*);
extern uint64_t fp_sqr(uint64_t*, uint64_t*);
extern uint64_t fp_exp_noct(uint64_t*, uint64_t*, uint64_t*);
extern uint64_t fp_inv(uint64_t*, uint64_t*);
extern uint64_t fp_toM(uint64_t*, uint64_t*);
extern uint64_t fp_fromM(uint64_t*, uint64_t*);
