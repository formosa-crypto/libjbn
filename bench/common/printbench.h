#ifndef PRINTBENCH_H
#define PRINTBENCH_H

#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>

# define cpucycles_fprintf_2(results,op_str)\
{\
  int op, loop;\
  uint64_t min;\
  FILE *f;\
\
  for (op = 0; op < OP; op++)\
  { min = results[op][0];\
    for (loop = 1; loop < LOOPS; loop++)\
    { if (min > results[op][loop])\
      { min = results[op][loop]; } }\
    results[op][0] = min;\
  }\
\
  for (op = 0; op < OP; op++)\
  { f = fopen(op_str[op], "w");\
    loop = 0;\
    fprintf(f, "%s, %" PRIu64 "\n", op_str[op], results[op][loop]);\
    fclose(f);\
  }\
}

#endif

