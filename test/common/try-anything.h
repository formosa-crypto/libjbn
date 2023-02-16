#ifndef TRY_ANYTHING
#define TRY_ANYTHING

#define CANARY_LENGTH 32

uint8_t* alignedcalloc(void**, uint64_t);
uint64_t* alignedcalloc_u64(void**, uint64_t);

void double_canary(uint8_t*, uint8_t*, uint64_t);
void double_canary_u64(uint64_t*, uint64_t*, uint64_t);

void input_prepare(uint8_t*, uint8_t*, uint64_t);
void input_prepare_u64(uint64_t*, uint64_t*, uint64_t);

void output_prepare(uint8_t*, uint8_t*, uint64_t);
void output_prepare_u64(uint64_t*, uint64_t*, uint64_t);

void output_compare(const uint8_t*, const uint8_t*, uint64_t, const char*);
void output_compare_u64(const uint64_t*, const uint64_t*, uint64_t, const char*);

void input_compare(const uint8_t*, const uint8_t*, uint64_t, const char *);
void input_compare_u64(const uint64_t*, const uint64_t*, uint64_t, const char *);

void checksum(uint8_t*, uint8_t*, uint64_t);
void checksum_u64(uint8_t*, uint64_t*, uint64_t);

unsigned long long myrandom(void);
void fail(const char *);
int try_anything_main(void);

#endif
