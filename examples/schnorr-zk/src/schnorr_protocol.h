#define NLIMBS 32

typedef uint64_t bignum[NLIMBS];

extern void commitment(
   uint64_t *commitment_p,      /* NLIMBS output  */
   uint64_t *random_power_p     /* NLIMBS output  */
);

extern void response(
   uint64_t *witness_p,         /* NLIMBS input */
   uint64_t *random_power_p,    /* NLIMBS input */
   uint64_t *challenge_p,       /* NLIMBS input */
   uint64_t *response_p         /* NLIMBS output */
);

extern void challenge(
   uint64_t *challenge_p        /* NLIMBS input */
);

extern void verify(
   uint64_t *statement_p,      /* NLIMBS input */
   uint64_t *commitment_p,     /* NLIMBS input */
   uint64_t *challenge_p,      /* NLIMBS input */
   uint64_t *response_p,       /* NLIMBS input */
   uint64_t *result_p          /* 64-word output */
);
