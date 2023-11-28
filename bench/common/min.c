#ifndef MIN_C
#define MIN_C

#include <inttypes.h>

#if defined(OP1)
static void min_1(uint64_t results[OP1][LOOPS])
{
  int op, loop;
  uint64_t min;

  // write min median of LOOP in results[op][0]
  for (op = 0; op < OP1; op++)
  { min = results[op][0];
    for (loop = 1; loop < LOOPS; loop++)
    { if (min > results[op][loop])
      { min = results[op][loop]; } }
    results[op][0] = min;
  }
}
#endif


#endif
