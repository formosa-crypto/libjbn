#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
//#include "i32_muladd.c"



br_muladd(uint64_t* a, uint64_t* b, uint64_t* c, uint64_t* d, uint64_t* e);

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
	uint64_t a[size+1],b[size],z,xlen,mlen;
	uint64_t val0, val1, val2;


	printf("\n -*- Testing Notes -*-\n\n When testing this function\n make sure the big number being\n divided is lower than m's value.\n\n If the above condition is not\n guaranted, the function fails.\n\n -*- Testing Notes -*-\n\n\n");

	// Test 1 - muladd last u64 

	for (int i = 0; i < size; ++i)
	{
		a[i] = 0;
		b[i] = 0;
	}
	a[size] = 0; // set last value

	val0 = 6;			// 8 = 1000
	val1 = 8;			// 8 = 1000
	a[0] = val0;
	b[0] = val1; 
	z = 8;      	  	// c == 1 means add
	xlen = 4;           // x bitlen
	mlen = 4;			// m bitlen
	br_muladd(a,&z,b,&xlen,&mlen);

	/* Result
		x = a
		m = b
		x = 6
		m = 8
		z = 8

		x * 2^64 + z % m
		= 6 * 2^64 + 8 % 8
		= (2^64 + 2^64 + 2^64 + 2^64 + 2^64 + 2^64) % 2^3 + 0 % 8
		= (2 + 2 + 2 + 2 + 2 + 2) % 2^3 + 0
		= 2*3 + 2*3 % 2^3
		= 0 % 8
	*/


	if (a[0] == 0)
	{
		printf("TEST 1 (MULADD LAST WORD).... PASSED!");
	} else {printf("TEST 1 (MULADD LAST WORD).... FAILED!"); print_a(a); }

	// Test 2 -  muladd multiple words
	for (int i = 0; i < size; ++i)
	{
		a[i] = 0;
		b[i] = 0;
	}
	a[size] = 0; // set last value

	a[0] = 8;
	a[1] = 8;
	b[0] = 8;
	b[1] = 8;
	z = 0;      	  	//
	xlen = 67;          // x bitlen
	mlen = 67;			// m bitlen

	/* Result
		x = a
		m = b
		x = (8*2^64 + 8) * 2^64
		m = (8*2^64 + 8)
		z = 0

		x + z % m 
		= ((8*2^64 + 8) * 2^64) % (8*2^64 + 8)
		= ((8*2^64 + 8) % (8*2^64 + 8) ) * 2^64
		= 0 * 2^64
		= 0	
	*/

	br_muladd(a,&z,b,&xlen,&mlen);

	if (a[0] == 0 & a[1] == 0 & a[2] == 0)
	{
		printf("\nTEST 2 (MULADD MULTIPLE WORDS).... PASSED!");
	} else {printf("\nTEST 2 (MULADD MULTIPLE WORDS).... FAILED!"); print_a(a); }

	// Test 3 - muladd for x value over m
	for (int i = 0; i < size; ++i)
	{
		a[i] = 0;
		b[i] = 0;
	}
	a[size] = 0; // set last value

	val0 = 1;
	val1 = 2;
	a[0] = 1;
	a[1] = 4;      // 0100
	b[0] = 0;		
	b[1] = 8;		// 1000
	z = 15;      	  	// 
	xlen = 67;          // x bitlen
	mlen = 68;			// m bitlen
	

	/* Result
		x = a
		m = b
		x = (4*2^64 + 1)
		m = (8*2^64)
		z = 15

		x + z % m 
		= ((4*2^64 + 1) * 2^64) + 15 % (8*2^64)
		= ((4*2^128 + 1*2^64) % (8*2^64)) + 15 % (8*2^64)
		= (4*2^128) % (8*2^64) + (2^64) % (8*2^64) + 15 % (8*2^64)
		= 0 % (8*2^64) + (2^64) % (8*2^64) + 15 % (8*2^64)
		= (2^64 + 15) % (8*2^64)
	*/

	br_muladd(a,&z,b,&xlen,&mlen);

	if (a[0] == 15 & a[1] == 1)
	{
		printf("\nTEST 3 (MULADD MULTIPLE WORDS).... PASSED!");
	} else {printf("\nTEST 3 (MULADD MULTIPLE WORDS).... FAILED!"); print_a(a); }


	// Test 4 - forcing modulo over several u64s
	for (int i = 0; i < size; ++i)
	{
		a[i] = 0;
		b[i] = 0;
	}
	a[size] = 0; // set last value

	val0 = 1;
	val1 = 2;
	a[0] = 0;
	a[1] = 0;
	a[2] = 0;
	a[3] = 0;
	a[4] = 8;
	b[0] = 0;
	b[1] = 0;
	b[2] = 0;
	b[3] = 0;
	b[4] = 12;
	z = 8;      	  	// c == 1 means add
	xlen = 260;         // x bitlen
	mlen = 260;			// m bitlen
	

	/* Result 
		x = a
		m = b
		x = 8 * 2^256
		m = 12 * 2^256
		z = 8
		
		x*2^64 + z % m
		= 8 * 2^256 * 2^64 % 12 * 2^256
		= 2^3 * 2^320 % (2^3+2^2)*2^256
		= 2^323 % (2^259+2^258)
		= 8 % (2^259+2^258)
	*/

	br_muladd(a,&z,b,&xlen,&mlen);

	if (a[0] == 8 & a[1] == 0 & a[2] == 0 & a[3] == 0 & a[4] == 8)
	{
		printf("\nTEST 4 (MULADD MULTIPLE WORDS).... PASSED!");
	} else {printf("\nTEST 4 (MULADD MULTIPLE WORDS).... FAILED!"); print_a(a); }

	printf("\n\n");


	return 0;
}




























