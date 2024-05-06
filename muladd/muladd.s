	.att_syntax
	.text
	.p2align	5
	.globl	_br_muladd
	.globl	br_muladd
_br_muladd:
br_muladd:
	movq	%rsp, %rax
	leaq	-584(%rsp), %rsp
	andq	$-32, %rsp
	movq	%rax, 576(%rsp)
	movq	%r15, 528(%rsp)
	movq	%r14, 536(%rsp)
	movq	%r13, 544(%rsp)
	movq	%r12, 552(%rsp)
	movq	%rbp, 560(%rsp)
	movq	%rbx, 568(%rsp)
	movq	(%rcx), %r9
	movq	(%rdi), %rax
	movq	%rax, 264(%rsp)
	movq	8(%rdi), %rax
	movq	%rax, 272(%rsp)
	movq	16(%rdi), %rax
	movq	%rax, 280(%rsp)
	movq	24(%rdi), %rax
	movq	%rax, 288(%rsp)
	movq	32(%rdi), %rax
	movq	%rax, 296(%rsp)
	movq	40(%rdi), %rax
	movq	%rax, 304(%rsp)
	movq	48(%rdi), %rax
	movq	%rax, 312(%rsp)
	movq	56(%rdi), %rax
	movq	%rax, 320(%rsp)
	movq	64(%rdi), %rax
	movq	%rax, 328(%rsp)
	movq	72(%rdi), %rax
	movq	%rax, 336(%rsp)
	movq	80(%rdi), %rax
	movq	%rax, 344(%rsp)
	movq	88(%rdi), %rax
	movq	%rax, 352(%rsp)
	movq	96(%rdi), %rax
	movq	%rax, 360(%rsp)
	movq	104(%rdi), %rax
	movq	%rax, 368(%rsp)
	movq	112(%rdi), %rax
	movq	%rax, 376(%rsp)
	movq	120(%rdi), %rax
	movq	%rax, 384(%rsp)
	movq	128(%rdi), %rax
	movq	%rax, 392(%rsp)
	movq	136(%rdi), %rax
	movq	%rax, 400(%rsp)
	movq	144(%rdi), %rax
	movq	%rax, 408(%rsp)
	movq	152(%rdi), %rax
	movq	%rax, 416(%rsp)
	movq	160(%rdi), %rax
	movq	%rax, 424(%rsp)
	movq	168(%rdi), %rax
	movq	%rax, 432(%rsp)
	movq	176(%rdi), %rax
	movq	%rax, 440(%rsp)
	movq	184(%rdi), %rax
	movq	%rax, 448(%rsp)
	movq	192(%rdi), %rax
	movq	%rax, 456(%rsp)
	movq	200(%rdi), %rax
	movq	%rax, 464(%rsp)
	movq	208(%rdi), %rax
	movq	%rax, 472(%rsp)
	movq	216(%rdi), %rax
	movq	%rax, 480(%rsp)
	movq	224(%rdi), %rax
	movq	%rax, 488(%rsp)
	movq	232(%rdi), %rax
	movq	%rax, 496(%rsp)
	movq	240(%rdi), %rax
	movq	%rax, 504(%rsp)
	movq	248(%rdi), %rax
	movq	%rax, 512(%rsp)
	movq	256(%rdi), %rax
	movq	%rax, 520(%rsp)
	movq	(%r8), %r8
	vmovdqu	(%rdx), %ymm0
	vmovdqu	%ymm0, (%rsp)
	vmovdqu	32(%rdx), %ymm0
	vmovdqu	%ymm0, 32(%rsp)
	vmovdqu	64(%rdx), %ymm0
	vmovdqu	%ymm0, 64(%rsp)
	vmovdqu	96(%rdx), %ymm0
	vmovdqu	%ymm0, 96(%rsp)
	vmovdqu	128(%rdx), %ymm0
	vmovdqu	%ymm0, 128(%rsp)
	vmovdqu	160(%rdx), %ymm0
	vmovdqu	%ymm0, 160(%rsp)
	vmovdqu	192(%rdx), %ymm0
	vmovdqu	%ymm0, 192(%rsp)
	vmovdqu	224(%rdx), %ymm0
	vmovdqu	%ymm0, 224(%rsp)
	movq	(%rsi), %rcx
	movq	%rdi, 256(%rsp)
	leaq	264(%rsp), %rsi
	movq	%rsp, %rdi
	call	L__br_muladd$1
Lbr_muladd$1:
	movq	256(%rsp), %rax
	movq	264(%rsp), %rcx
	movq	%rcx, (%rax)
	movq	272(%rsp), %rcx
	movq	%rcx, 8(%rax)
	movq	280(%rsp), %rcx
	movq	%rcx, 16(%rax)
	movq	288(%rsp), %rcx
	movq	%rcx, 24(%rax)
	movq	296(%rsp), %rcx
	movq	%rcx, 32(%rax)
	movq	304(%rsp), %rcx
	movq	%rcx, 40(%rax)
	movq	312(%rsp), %rcx
	movq	%rcx, 48(%rax)
	movq	320(%rsp), %rcx
	movq	%rcx, 56(%rax)
	movq	328(%rsp), %rcx
	movq	%rcx, 64(%rax)
	movq	336(%rsp), %rcx
	movq	%rcx, 72(%rax)
	movq	344(%rsp), %rcx
	movq	%rcx, 80(%rax)
	movq	352(%rsp), %rcx
	movq	%rcx, 88(%rax)
	movq	360(%rsp), %rcx
	movq	%rcx, 96(%rax)
	movq	368(%rsp), %rcx
	movq	%rcx, 104(%rax)
	movq	376(%rsp), %rcx
	movq	%rcx, 112(%rax)
	movq	384(%rsp), %rcx
	movq	%rcx, 120(%rax)
	movq	392(%rsp), %rcx
	movq	%rcx, 128(%rax)
	movq	400(%rsp), %rcx
	movq	%rcx, 136(%rax)
	movq	408(%rsp), %rcx
	movq	%rcx, 144(%rax)
	movq	416(%rsp), %rcx
	movq	%rcx, 152(%rax)
	movq	424(%rsp), %rcx
	movq	%rcx, 160(%rax)
	movq	432(%rsp), %rcx
	movq	%rcx, 168(%rax)
	movq	440(%rsp), %rcx
	movq	%rcx, 176(%rax)
	movq	448(%rsp), %rcx
	movq	%rcx, 184(%rax)
	movq	456(%rsp), %rcx
	movq	%rcx, 192(%rax)
	movq	464(%rsp), %rcx
	movq	%rcx, 200(%rax)
	movq	472(%rsp), %rcx
	movq	%rcx, 208(%rax)
	movq	480(%rsp), %rcx
	movq	%rcx, 216(%rax)
	movq	488(%rsp), %rcx
	movq	%rcx, 224(%rax)
	movq	496(%rsp), %rcx
	movq	%rcx, 232(%rax)
	movq	504(%rsp), %rcx
	movq	%rcx, 240(%rax)
	movq	512(%rsp), %rcx
	movq	%rcx, 248(%rax)
	movq	520(%rsp), %rcx
	movq	%rcx, 256(%rax)
	movq	528(%rsp), %r15
	movq	536(%rsp), %r14
	movq	544(%rsp), %r13
	movq	552(%rsp), %r12
	movq	560(%rsp), %rbp
	movq	568(%rsp), %rbx
	movq	576(%rsp), %rsp
	ret
L__br_muladd$1:
	cmpq	$65, %r8
	jb  	L__br_muladd$2
	addq	$63, %r8
	shrq	$6, %r8
	addq	$-1, %r8
	movq	(%rsi,%r8,8), %r10
	movq	(%rsi,%r8,8), %rax
	movq	%r8, %rdx
	addq	$-1, %rdx
	movq	%r8, %rbp
	call	Lcopy_array$1
L__br_muladd$11:
	movq	%rcx, (%rsi)
	movq	(%rsi,%r8,8), %rbp
	movq	(%rdi,%r8,8), %rdx
	movq	%rax, %r11
	movq	%rdx, %r12
	movq	%rbx, %rcx
	movq	%r13, %rbx
	leaq	-16(%rsp), %rsp
	call	L__divrem$1
L__br_muladd$10:
	leaq	16(%rsp), %rsp
	movq	%rbx, %rcx
	addq	$-1, %rcx
	movq	$0, %r11
	cmpq	$0, %rbx
	cmove	%r11, %rcx
	cmpq	%rax, %rdx
	movq	%rcx, %r11
	movq	$-1, %rax
	cmovp	%rax, %r11
	movq	$0, %r13
	movq	$0, %r12
	movq	$1, %rcx
	movq	$0, %rbx
	jmp 	L__br_muladd$8
L__br_muladd$9:
	movq	(%rdi,%rbx,8), %rbp
	movq	%r11, %rax
	mulq	%rbp
	addq	%r12, %rax
	adcq	%r13, %rdx
	movq	%rdx, %r12
	movq	$0, %r13
	movq	$1, %rdx
	cmovb	%rdx, %r13
	movq	(%rsi,%rbx,8), %rdx
	subq	%rax, %rdx
	adcq	$0, %r12
	movq	%rdx, (%rsi,%rbx,8)
	cmpq	%rbp, %rdx
	movq	$1, %rax
	movq	$0, %rdx
	cmovb	%rdx, %rax
	movq	$0, %rdx
	movq	$1, %rbp
	cmovp	%rbp, %rdx
	andq	%rdx, %rax
	cmpq	$1, %rdx
	cmove	%rax, %rcx
	incq	%rbx
L__br_muladd$8:
	cmpq	%r8, %rbx
	jbe 	L__br_muladd$9
	cmpq	%r10, %r12
	movq	$0, %rax
	movq	$1, %rdx
	cmovb	%rdx, %rax
	orq 	%r13, %rax
	cmpq	%r10, %r12
	movq	$0, %rdx
	movq	$1, %r8
	cmovb	%r8, %rdx
	xorq	$-1, %r13
	andq	%rdx, %r13
	orq 	%r13, %rcx
	movq	%rax, %rdx
	xorq	$-1, %rdx
	andq	%rcx, %rdx
	leaq	-8(%rsp), %rsp
	call	L__br_add$1
L__br_muladd$7:
	leaq	8(%rsp), %rsp
	leaq	-8(%rsp), %rsp
	call	L__br_sub$1
L__br_muladd$6:
	leaq	8(%rsp), %rsp
	jmp 	L__br_muladd$3
L__br_muladd$2:
	cmpq	$0, %r8
	je  	L__br_muladd$3
	movq	(%rsi), %r11
	movq	%rcx, %rbp
	movq	(%rdi), %r12
	movq	%rdx, %rcx
	movq	%rax, %rbx
	leaq	-16(%rsp), %rsp
	call	L__divrem$1
L__br_muladd$5:
	leaq	16(%rsp), %rsp
	movq	%rbp, %rax
	movq	%rax, (%rsi)
L__br_muladd$4:
L__br_muladd$3:
	ret
Lcopy_array$1:
	jmp 	Lcopy_array$2
Lcopy_array$3:
	movq	(%rsi,%rdx,8), %r11
	movq	%r11, (%rsi,%rbp,8)
	movq	%rdx, %rbp
	addq	$-1, %rdx
Lcopy_array$2:
	cmpq	$0, %rdx
	jnbe	Lcopy_array$3
	movq	(%rsi,%rdx,8), %rdx
	movq	%rdx, (%rsi,%rbp,8)
	ret
L__br_sub$1:
	addq	$63, %r9
	shrq	$6, %r9
	movq	$0, %r10
	movq	$0, %r11
	jmp 	L__br_sub$2
L__br_sub$3:
	movq	(%rsi,%r11,8), %rax
	movq	(%rdi,%r11,8), %rcx
	movq	%r11, 8(%rsp)
	movq	%rax, %r8
	addq	%r10, %rcx
	subq	%rcx, %r8
	movq	$0, %r10
	movq	$1, %rcx
	cmovb	%rcx, %r10
	cmpq	$1, %rdx
	cmove	%r8, %rax
	movq	%rax, (%rsi,%r11,8)
	movq	8(%rsp), %r11
	incq	%r11
L__br_sub$2:
	cmpq	%r9, %r11
	jb  	L__br_sub$3
	ret
L__br_add$1:
	movq	%r9, %rcx
	addq	$127, %rcx
	shrq	$6, %rcx
	movq	$0, %r8
	xorq	%r8, %r8
	movq	$0, %rbp
	movq	$0, %r12
	jmp 	L__br_add$2
L__br_add$3:
	movq	(%rsi,%r12,8), %r10
	movq	(%rdi,%r12,8), %r11
	movq	%r8, 8(%rsp)
	movq	%r10, %r8
	addq	%r11, %r8
	movq	$0, %r11
	movq	$1, %rbx
	cmovb	%rbx, %r11
	addq	%rbp, %r8
	movq	$0, %rbp
	cmovb	%rbx, %rbp
	orq 	%r11, %rbp
	cmpq	$1, %rax
	cmove	%r8, %r10
	movq	%r10, (%rsi,%r12,8)
	movq	8(%rsp), %r12
	incq	%r12
L__br_add$2:
	cmpq	%rcx, %r12
	jbe 	L__br_add$3
	ret
L__divrem$1:
	cmpq	%r12, %r11
	movq	$0, %rcx
	cmove	%rcx, %r11
	movq	$0, %rbx
	movq	$63, %r13
	jmp 	L__divrem$2
L__divrem$3:
	movq	$64, %rcx
	subq	%r13, %rcx
	movq	%r13, 8(%rsp)
	movq	%r11, %r13
	shldq	%cl, %rbp, %r13
	movq	%rcx, 16(%rsp)
	cmpq	%r12, %r13
	movq	$1, %r15
	movq	$0, %rcx
	cmovb	%rcx, %r15
	movq	%r11, %r14
	movq	8(%rsp), %rcx
	shrq	%cl, %r14
	cmpq	$0, %r14
	movq	$1, %r14
	movq	$0, %rcx
	cmovp	%rcx, %r14
	orq 	%r15, %r14
	subq	%r12, %r13
	movq	16(%rsp), %rcx
	shrq	%cl, %r13
	movq	%r12, %r15
	movq	8(%rsp), %rcx
	shlq	%cl, %r15
	movq	%rbp, %rcx
	subq	%r15, %rcx
	cmpq	$1, %r14
	cmove	%r13, %r11
	cmpq	$1, %r14
	cmove	%rcx, %rbp
	movq	8(%rsp), %rcx
	shlq	%cl, %r14
	orq 	%r14, %rbx
	movq	8(%rsp), %r13
	addq	$-1, %r13
L__divrem$2:
	cmpq	$0, %r13
	jnbe	L__divrem$3
	cmpq	%r12, %rbp
	movq	$1, %rcx
	movq	$0, %r13
	cmovb	%r13, %rcx
	orq 	%rcx, %r11
	orq 	%r11, %rbx
	movq	%rbp, %rcx
	subq	%r12, %rcx
	cmpq	$1, %r11
	cmove	%rcx, %rbp
	ret
