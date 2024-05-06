
// Test Vectors


#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "i32_div32.c"

void divrem(uint64_t* a, uint64_t* b, uint64_t* c, uint64_t* d, uint64_t* e);


int main()
{
	/* Original Special Case
		uint32_t input1, input2, input3,q,r;
		
		input1 = 8;
		input2 = 8;
		input3 = 8;

		printf("\nStarting br_divrem:\n\n");
		q = br_divrem(input1, input2, input3, &r);

		printf("r = %u\n", r);
		printf("q = %u\n", q);
	*/
	uint64_t a,b,c,d,e;

	/* Test 1 - Special Case: hi == d => q = 1; r = 0; */
	a = 8;
	b = 8; // 11 = 1011
	c = 8;


	divrem(&a,&b,&c,&d,&e);

	if (d == 1 & e == 0)
	{
		printf("\nTEST 1 (DIV MULTIPLE WORD).... PASSED!");
	} else {printf("\nTEST 1 (DIV MULTIPLE WORD).... FAILED!"); }


	/*
	a = 0;
	b = input1;
	b <<= 32;
	b |= input2;
	c = b0;
	*/

	/* Test 2 - Random numbers */
	a = 9;
	b = 0; // 11 = 1011
	c = 8;

	divrem(&a,&b,&c,&d,&e);
	
	char * str;

	if ((float)(d * c + e - pow(2,64) * a - b) <= 0.00000000001)
	{
		printf("\nTEST 2 (DIV MULTIPLE WORD).... PASSED!");
	} else {printf("\nTEST 2 (DIV MULTIPLE WORD).... FAILED!"); }

	printf("\n\n");

	return 0;
}






