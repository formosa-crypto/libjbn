#ifndef TEST_MISC_BARRETT
#define TEST_MISC_BARRETT

#include <stdint.h>
#include <gmp.h>

void barrett_precompute(uint64_t *barrett_factor, uint64_t *mod, size_t NLIMBS);

//

void barrett_print_jasmin(
  uint64_t *barrett_factor,
  size_t NLIMBS,
  FILE *fout
);

void barrett_print_c(
  uint64_t *barrett_factor,
  size_t NLIMBS,
  FILE *fout
);

#endif
