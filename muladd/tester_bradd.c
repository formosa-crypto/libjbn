
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>


br_add(uint64_t* a, uint64_t* b, uint64_t* c, uint64_t* d);

printa(uint64_t a[33])
{
	printf("\na = {");
	for (int i = 0; i < 33; ++i)
	{
		printf("%llu, ",a[i] );
	}
	printf("}\n\n");
}

int main()
{
	
	int size = 32;
	uint64_t a[size+1],b[size],c,d;
	uint64_t val0, val1, val2;


	printf("\n");

	/* Test 1 - sum last u64 */
	for (int i = 0; i < size; ++i)
	{
		a[i] = 0;
		b[i] = 0;
	}
	a[size] = 0; // set last value

	val0 = 10;
	val1 = 15;
	val2 = val0 + val1;
	a[size] = val0;   // 10 = 1010
	b[size-1] = val1; // 15 = 1111
	c = 1;      	  // c == 1 means add
	d = 4;            // x bitlen

	br_add(a,b,&c,&d);

	if (a[size] == val2)
	{
		printf("TEST 1 (SUM LAST WORD).... PASSED!");
	} else {printf("TEST 1 (SUM LAST WORD).... FAILED!"); printa(a); }

	/* Test 2 - sum multiple words */
	for (int i = 0; i < size; ++i)
	{
		a[i] = 0;
		b[i] = 0;
	}
	a[size] = 0; // set last value

	val0 = 30 + 34567;
	val1 = 35 + 3456;
	a[size] = 30; 
	a[size-1] = 35;
	b[size-1] = 34567;
	b[size-2] = 3456;
	c = 1; 	    // c == 1 means add
	d = 5 + 64; // x bitlen

	br_add(a,b,&c,&d);

	if (a[size] == val0 & a[size-1] == val1)
	{
		printf("\nTEST 2 (SUM MULTIPLE WORDS).... PASSED!");
	} else {printf("\nTEST 2 (SUM MULTIPLE WORDS).... FAILED!"); printa(a); }

	/* Test 3 - forcing carry bits across 2 u64 words */
	for (int i = 0; i < size; ++i)
	{
		a[i] = 0;
		b[i] = 0;
	}
	a[size] = 0; // set last value


	val0 = 18446744073709551615; // full u64 word
	val1 = 18446744073709551614;
	a[size] = val0;
	b[size-1] = val0;
	c = 1; 	   // c == 1 means add
	d = 64;     // x bitlen
	
	br_add(a,b,&c,&d);

	if (a[size] == val1 & a[size-1] == 1)
	{
		printf("\nTEST 3 (SUM MULTIPLE WORDS).... PASSED!");
	} else {printf("\nTEST 3 (SUM MULTIPLE WORDS).... FAILED!"); printa(a); }

	/* Test 4 - forcing carry bits across multiple u64 words */
	for (int i = 0; i < size; ++i)
	{
		a[i] = 0;
		b[i] = 0;
	}
	a[size] = 0; // set last value


	val0 = 18446744073709551615; // full u64 word
	val1 = 18446744073709551614;
	a[size] = val0;
	a[size-1] = val0;
	a[size-2] = 1;
	b[size-1] = val0;
	b[size-2] = val0;
	c = 1;  	   // c == 1 means add
	d = 129;       // x bitlen
	
	br_add(a,b,&c,&d);

	if (a[size] == val1 & a[size-1] == val0 & a[size-2] == 2)
	{
		printf("\nTEST 4 (SUM MULTIPLE WORDS).... PASSED!");
	} else {printf("\nTEST 4 (SUM MULTIPLE WORDS).... FAILED!"); printa(a); }

	printf("\n\n");
	return 0;
}











