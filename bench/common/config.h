#ifndef CONFIG_H
#define CONFIG_H

//

#ifndef RUNS
#define RUNS 10
#endif

#ifndef LOOPS
#define LOOPS 1
#endif

#ifndef TIMINGS
#define TIMINGS 10001
#endif

//

#if defined(ST_ON)

 #ifndef ST_MAX
 #define ST_MAX 2
 #endif

 // 1 %
 #ifndef ST_PER
 #define ST_PER 1
 #endif

 #ifndef ST_CHK
 #define ST_CHK (((double)ST_PER)/((double)100.0))
 #endif

#endif
//

#endif

