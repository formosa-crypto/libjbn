#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//

#include "bn_generic.c"
#include "fp_generic.c"

//

int main(void)
{
  int r;

  r  = bn_generic_main();
  r |= fn_generic_main();
  
  return r;
}

