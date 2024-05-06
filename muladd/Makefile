all: muladd

full:
	clear
	jasminc -o divrem.s jazzcode/divrem.jazz
	jasminc -o add.s jazzcode/br_add.jazz
	jasminc -o sub.s jazzcode/br_sub.jazz
	jasminc -o muladd.s jazzcode/muladd.jazz

brdiv:
	clear & jasminc -o divrem.s jazzcode/divrem.jazz
	clear & gcc divrem.s tester_brdiv.c
	clear & ./a.out

bradd:
	clear & jasminc -o add.s jazzcode/br_add.jazz
	clear & gcc add.s tester_bradd.c
	clear & ./a.out

brsub:
	clear & jasminc -o sub.s jazzcode/br_sub.jazz
	clear & gcc sub.s tester_brsub.c
	clear & ./a.out

muladd:
	clear & jasminc -o muladd.s jazzcode/muladd.jazz
	clear & gcc muladd.s tester_muladd.c
	clear & ./a.out


