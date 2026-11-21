#ifndef STABILITY_C
#define STABILITY_C

#if defined(NOTRANDOMBYTES_H)
  #define _st_internal_reset_randombytes resetrandombytes(); resetrandombytes1();
  #define _st_randombytes0(a,b) randombytes(a,b)
  #define _st_randombytes1(a,b) randombytes1(a,b)
#else
  #define _st_internal_reset_randombytes
  #define _st_randombytes0(a,b) randombytes(a,b)
  #define _st_randombytes1(a,b) randombytes(a,b)
#endif

#if defined(ST_ON)

// RUNS must be > 1
#if (RUNS <= 1)
#error "error: stability.c : RUNS should be greater or equal than 2"
#endif

// assuming sizeof(uint64_t) == sizeof(unsigned long)
#define _st_static_check(c) ((void)sizeof(char[0 - (int)!(c)]))
void check_uint64_t_ulong(void){ _st_static_check(sizeof(uint64_t) == sizeof(unsigned long)); }

// includes
#include "config.h"
#include "cpucycles.c" // cmp_uint64
#include <gsl/gsl_statistics_ulong.h> // gsl_stats_ulong_{mean,sd}

// common macros / functions

#define _st_while_b int _st_ok = 0, _st_it = ST_MAX; while(_st_it > 0 && _st_ok == 0){
#define _st_while_e _st_it--; }
#define _st_reset_randombytes _st_internal_reset_randombytes
#define _st_ifnotst(a)

static uint64_t st_median(uint64_t *r, size_t length)
{
  if((length & 1) == 1)
  { return r[length>>1]; }
  else
  { return (r[(length>>1)-1] + r[(length>>1)]) >> 1; }
}

// OPx specific macros

// ////////////////////////////////////////////////////////////////////////////
#if defined(OP1)

 #define _st_store_1(median_r, run, median_l) st_store_1(median_r, run, median_l);
 #define _st_check_1(sd_r, mean_r, median_r) if(st_check_1(sd_r, mean_r, median_r) == 1){ _st_ok = 1; }
 #define _st_print_1(argc, sd_r, mean_r, median_r, op1_str, op1_str_short) st_print_1(argc, _st_it, _st_ok, sd_r, mean_r, median_r, op1_str, op1_str_short);

 static void st_store_1(uint64_t median_runs[OP1][RUNS], int run, uint64_t median_loops[OP1][LOOPS])
 {
   size_t op;
   min_1(median_loops);
   for (op = 0; op < OP1; op++)
   { median_runs[op][run] = median_loops[op][0]; }
 }

 static int st_check_1(double sd_runs[OP1], double mean_runs[OP1], uint64_t median_runs[OP1][RUNS])
 {
   size_t op;
   double mean, sd;
   int ok = 1;
 
   for (op = 0; op < OP1; op++)
   {
     qsort(&(median_runs[op][0]), RUNS, sizeof(uint64_t), cmp_uint64);
 
     mean = gsl_stats_ulong_mean(&(median_runs[op][0]), 1, RUNS);
     sd   = gsl_stats_ulong_sd(&(median_runs[op][0]), 1, RUNS);
 
     mean_runs[op] = mean;
     sd_runs[op]   = sd;

     // TODO fine-tune this // isolate
     if(sd > (mean * ST_CHK))
     { ok = 0; }
   }
 
   return ok;
 }

 static void st_print_1(
  int argc,
  int _st_it,
  int _st_ok,
  double sd_runs[OP1],
  double mean_runs[OP1],
  uint64_t median_runs[OP1][RUNS],
  char *op_str[],
  char *op_str_short[])
 {
   size_t op, run;
   FILE *f;

   // print to file or stdout: number_of_iterations, check_is_ok, sdev, mean, median, list_of_results 
   f = stdout;
   for (op = 0; op < OP1; op++)
   { if(argc == 1) { f = fopen(op_str[op], "a"); }
     else          { fprintf(f, "%s, ", op_str_short[op]); }
     fprintf(f, "%d, %d", (ST_MAX-_st_it), _st_ok);
     fprintf(f, ", %.2lf, %.2lf, %" PRIu64 "", sd_runs[op], mean_runs[op], st_median(&(median_runs[op][0]), RUNS));

     for(run = 0; run < RUNS-1; run++)
     { fprintf(f, ", %" PRIu64 "", median_runs[op][run]); }
     fprintf(f, ", %" PRIu64 "\n", median_runs[op][RUNS-1]);

     if(argc == 1) { fclose(f); }
   }
 }

#endif

// ////////////////////////////////////////////////////////////////////////////

#else // defined(ST_ON)

 #define _st_while_b
 #define _st_while_e
 #define _st_reset_randombytes
 #define _st_ifnotst(a) a;

 #define _st_store_1(median_r, run, median_loops)
 #define _st_check_1(sd_r, mean_r, median_r)
 #define _st_print_1(argc, sd_r, mean_r, median_r, op1_str, op1_str_short)

#endif

#endif // STABILITY_C
