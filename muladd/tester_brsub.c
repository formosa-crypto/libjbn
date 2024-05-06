
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>


br_sub(uint64_t* a, uint64_t* b, uint64_t* c, uint64_t* d);

void print_a(uint64_t a[33])
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

	/* Test 1 - subtract last u64 */
	for (int i = 0; i < size; ++i)
	{
		a[i] = 0;
		b[i] = 0;
	}
	a[size] = 0; // set last value

	val0 = 15;
	val1 = 10;
	val2 = val0 - val1;
	a[size] = val0;   // 10 = 1010
	b[size-1] = val1; // 15 = 1111
	c = 1;      	  // c == 1 means add
	d = 4;            // x bitlen

	br_sub(a,b,&c,&d);

	if (a[size] == val2)
	{
		printf("TEST 1 (SUBTRACT LAST WORD).... PASSED!");
	} else {printf("TEST 1 (SUBTRACT LAST WORD).... FAILED!"); print_a(a); }

	// Test 2 - subtract multiple words
	for (int i = 0; i < size; ++i)
	{
		a[i] = 0;
		b[i] = 0;
	}
	a[size] = 0; // set last value

	val0 = 5;
	val1 = 5;
	a[size] = 35; 
	a[size-1] = 35;
	b[size-1] = 30;
	b[size-2] = 30;
	c = 1; 	    // c == 1 means add
	d = 6 + 64; // x bitlen

	br_sub(a,b,&c,&d);

	if (a[size] == val0 & a[size-1] == val1)
	{
		printf("\nTEST 2 (SUBTRACT MULTIPLE WORDS).... PASSED!");
	} else {printf("\nTEST 2 (SUBTRACT MULTIPLE WORDS).... FAILED!"); print_a(a); }

	// Test 3 - forcing carry bits across 2 u64 words
	for (int i = 0; i < size; ++i)
	{
		a[i] = 0;
		b[i] = 0;
	}
	a[size] = 0; // set last value


	val0 = 1;
	val1 = 2;
	a[size] = 0;
	a[size-1] = 1;
	b[size-1] = 128;
	c = 1; 	    // c == 1 means add
	d = 65;     // x bitlen
	
	br_sub(a,b,&c,&d);

	if ((float)a[size] == (pow(2,64)-128) & a[size-1] == 0)
	{
		printf("\nTEST 3 (SUBTRACT MULTIPLE WORDS).... PASSED!");
	} else {printf("\nTEST 3 (SUBTRACT MULTIPLE WORDS).... FAILED!"); print_a(a); }

	// Test 4 - forcing carry bits across multiple u64 words
	for (int i = 0; i < size; ++i)
	{
		a[i] = 0;
		b[i] = 0;
	}
	a[size] = 0; // set last value

	val0 = 1;
	val1 = 2;
	a[size] = 0;
	a[size-1] = 0;
	a[size-2] = 1;
	b[size-1] = val0;
	b[size-2] = val0;
	b[size-2] = 0;
	c = 1;  	   // c == 1 means add
	d = 129;       // x bitlen
	
	br_sub(a,b,&c,&d);

	if ((float)a[size] == (pow(2,64)-1) & (float)a[size-1] == (pow(2,64)-1) & a[size-2] == 0)
	{
		printf("\nTEST 4 (SUBTRACT MULTIPLE WORDS).... PASSED!");
	} else {printf("\nTEST 4 (SUBTRACT MULTIPLE WORDS).... FAILED!"); print_a(a); }

	printf("\n\n");
	return 0;
}











