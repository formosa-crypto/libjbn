	.att_syntax
	.text
	.p2align	5
	.globl	_gf_inv_jazz
	.globl	gf_inv_jazz
	.globl	_gf_normalize_jazz
	.globl	gf_normalize_jazz
_gf_inv_jazz:
gf_inv_jazz:
	movq	%rsp, %rax
	leaq	-136(%rsp), %rsp
	andq	$-32, %rsp
	movq	%rax, 128(%rsp)
	movq	%r15, 80(%rsp)
	movq	%r14, 88(%rsp)
	movq	%r13, 96(%rsp)
	movq	%r12, 104(%rsp)
	movq	%rbp, 112(%rsp)
	movq	%rbx, 120(%rsp)
	vmovdqu	(%rdi), %ymm0
	vmovdqu	%ymm0, (%rsp)
	vmovdqu	(%rsi), %ymm0
	vmovdqu	%ymm0, 32(%rsp)
	movq	%rdi, 64(%rsp)
	movq	%rdx, 72(%rsp)
	movq	%rsp, %rax
	leaq	32(%rsp), %rdi
	leaq	-288(%rsp), %rsp
	call	L__gf_inv$1
Lgf_inv_jazz$1:
	leaq	288(%rsp), %rsp
	movq	64(%rsp), %rax
	vmovdqu	(%rsp), %ymm0
	vmovdqu	%ymm0, (%rax)
	movq	72(%rsp), %rax
	movq	$0, (%rax)
	movq	80(%rsp), %r15
	movq	88(%rsp), %r14
	movq	96(%rsp), %r13
	movq	104(%rsp), %r12
	movq	112(%rsp), %rbp
	movq	120(%rsp), %rbx
	movq	128(%rsp), %rsp
	ret
_gf_normalize_jazz:
gf_normalize_jazz:
	movq	%rsp, %rax
	leaq	-88(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rax, 80(%rsp)
	movq	%rbx, 72(%rsp)
	movq	(%rdi), %rax
	movq	%rax, 8(%rsp)
	movq	8(%rdi), %rax
	movq	%rax, 16(%rsp)
	movq	16(%rdi), %rax
	movq	%rax, 24(%rsp)
	movq	24(%rdi), %rax
	movq	%rax, 32(%rsp)
	movq	(%rsi), %rax
	movq	%rax, 40(%rsp)
	movq	8(%rsi), %rax
	movq	%rax, 48(%rsp)
	movq	16(%rsi), %rax
	movq	%rax, 56(%rsp)
	movq	24(%rsi), %rax
	movq	%rax, 64(%rsp)
	movq	%rdi, (%rsp)
	leaq	8(%rsp), %rcx
	leaq	40(%rsp), %rdi
	call	L__gf_normalize$1
Lgf_normalize_jazz$1:
	movq	(%rsp), %rax
	movq	8(%rsp), %rcx
	movq	%rcx, (%rax)
	movq	16(%rsp), %rcx
	movq	%rcx, 8(%rax)
	movq	24(%rsp), %rcx
	movq	%rcx, 16(%rax)
	movq	32(%rsp), %rcx
	movq	%rcx, 24(%rax)
	movq	72(%rsp), %rbx
	movq	80(%rsp), %rsp
	ret
L__gf_inv$1:
	leaq	72(%rsp), %rcx
	call	L__gf_normalize$1
L__gf_inv$20:
	leaq	40(%rsp), %rcx
	leaq	glob_data + 32(%rip), %rdx
	call	L__copy_gf$1
L__gf_inv$19:
	leaq	104(%rsp), %rcx
	leaq	glob_data + 64(%rip), %rdx
	call	L__copy_gf$1
L__gf_inv$18:
	leaq	136(%rsp), %rcx
	leaq	glob_data + 96(%rip), %rdx
	call	L__copy_gf$1
L__gf_inv$17:
	movq	%rax, 8(%rsp)
	movq	$0, %rax
	jmp 	L__gf_inv$6
L__gf_inv$7:
	movq	%rax, 16(%rsp)
	movq	96(%rsp), %rax
	movq	64(%rsp), %rcx
	orq 	%rax, %rcx
	movq	88(%rsp), %rax
	movq	56(%rsp), %rdx
	orq 	%rax, %rdx
	movq	%rdx, %rdi
	movq	80(%rsp), %rax
	movq	48(%rsp), %rdx
	orq 	%rax, %rdx
	movq	%rdx, %r8
	movq	%rcx, %rax
	negq	%rax
	movq	%rcx, %rdx
	orq 	%rdx, %rax
	shrq	$63, %rax
	negq	%rax
	movq	%rdi, %rdx
	negq	%rdx
	orq 	%rdi, %rdx
	shrq	$63, %rdx
	negq	%rdx
	movq	%rax, %rsi
	xorq	$-1, %rsi
	andq	%rdx, %rsi
	movq	%rsi, %rdx
	movq	%r8, %rsi
	negq	%rsi
	orq 	%r8, %rsi
	shrq	$63, %rsi
	negq	%rsi
	movq	%rax, %r9
	xorq	$-1, %r9
	andq	%rsi, %r9
	movq	%rdx, %rsi
	xorq	$-1, %rsi
	andq	%r9, %rsi
	andq	%rax, %rcx
	andq	%rdx, %rdi
	orq 	%rdi, %rcx
	andq	%rsi, %r8
	orq 	%r8, %rcx
	movq	96(%rsp), %rdi
	andq	%rax, %rdi
	movq	88(%rsp), %r8
	andq	%rdx, %r8
	orq 	%r8, %rdi
	movq	80(%rsp), %r8
	andq	%rsi, %r8
	orq 	%r8, %rdi
	movq	64(%rsp), %r8
	andq	%rax, %r8
	movq	56(%rsp), %r9
	andq	%rdx, %r9
	orq 	%r9, %r8
	movq	48(%rsp), %r9
	andq	%rsi, %r9
	orq 	%r9, %r8
	movq	88(%rsp), %r9
	andq	%rax, %r9
	movq	80(%rsp), %r10
	andq	%rdx, %r10
	orq 	%r10, %r9
	movq	72(%rsp), %r10
	andq	%rsi, %r10
	orq 	%r10, %r9
	movq	56(%rsp), %r10
	andq	%rax, %r10
	movq	48(%rsp), %r11
	andq	%rdx, %r11
	orq 	%r11, %r10
	movq	40(%rsp), %r11
	andq	%rsi, %r11
	orq 	%r11, %r10
	lzcntq	%rcx, %r11
	movq	$31, %rbx
	subq	%r11, %rbx
	movq	$63, %rcx
	shrq	%cl, %rbx
	negq	%rbx
	movq	%rdi, %rbp
	movq	$32, %rcx
	shlq	%cl, %rbp
	shrq	%cl, %r9
	orq 	%r9, %rbp
	movq	%rdi, %rcx
	xorq	%rbp, %rcx
	andq	%rbx, %rcx
	xorq	%rcx, %rdi
	movq	%r8, %r9
	movq	$32, %rcx
	shlq	%cl, %r9
	shrq	%cl, %r10
	orq 	%r10, %r9
	movq	%r8, %rcx
	xorq	%r9, %rcx
	andq	%rbx, %rcx
	xorq	%rcx, %r8
	movq	$32, %rcx
	andq	%rbx, %rcx
	subq	%rcx, %r11
	movq	%r11, %rcx
	shlq	%cl, %rdi
	shlq	%cl, %r8
	orq 	%rdx, %rsi
	orq 	%rax, %rsi
	xorq	$-1, %rsi
	movq	72(%rsp), %rax
	andq	%rsi, %rax
	orq 	%rax, %rdi
	movq	40(%rsp), %rax
	andq	%rsi, %rax
	orq 	%rax, %r8
	movq	72(%rsp), %rax
	andq	$2147483647, %rax
	andq	$-2147483648, %rdi
	orq 	%rdi, %rax
	movq	40(%rsp), %rcx
	andq	$2147483647, %rcx
	andq	$-2147483648, %r8
	orq 	%r8, %rcx
	call	L__asm_volatile$1
L__gf_inv$16:
	leaq	264(%rsp), %rbp
	leaq	72(%rsp), %rax
	leaq	40(%rsp), %rdx
	movq	%rdi, %rsi
	movq	%r12, %r8
	leaq	-96(%rsp), %rsp
	call	L__s256_lin_div31_abs$1
L__gf_inv$15:
	leaq	96(%rsp), %rsp
	movq	%rdx, 24(%rsp)
	leaq	232(%rsp), %rbp
	leaq	72(%rsp), %rax
	leaq	40(%rsp), %rdx
	movq	%r11, %rsi
	movq	%rcx, %r8
	leaq	-96(%rsp), %rsp
	call	L__s256_lin_div31_abs$1
L__gf_inv$14:
	leaq	96(%rsp), %rsp
	movq	%rdx, 32(%rsp)
	movq	24(%rsp), %rax
	negq	%rax
	xorq	%rax, %rdi
	movq	24(%rsp), %rdx
	addq	%rdx, %rdi
	xorq	%rax, %r12
	movq	24(%rsp), %rax
	addq	%rax, %r12
	movq	32(%rsp), %rax
	negq	%rax
	xorq	%rax, %r11
	movq	32(%rsp), %rdx
	addq	%rdx, %r11
	xorq	%rax, %rcx
	movq	32(%rsp), %rax
	addq	%rax, %rcx
	movq	%r11, 32(%rsp)
	movq	%rcx, 24(%rsp)
	leaq	200(%rsp), %r8
	leaq	104(%rsp), %rdx
	leaq	136(%rsp), %rax
	movq	%r12, %rcx
	leaq	-80(%rsp), %rsp
	call	L__gf_lin$1
L__gf_inv$13:
	leaq	80(%rsp), %rsp
	movq	32(%rsp), %rdi
	movq	24(%rsp), %rcx
	leaq	168(%rsp), %r8
	leaq	104(%rsp), %rdx
	leaq	136(%rsp), %rax
	leaq	-80(%rsp), %rsp
	call	L__gf_lin$1
L__gf_inv$12:
	leaq	80(%rsp), %rsp
	leaq	72(%rsp), %rcx
	leaq	264(%rsp), %rdx
	call	L__copy_gf$1
L__gf_inv$11:
	leaq	40(%rsp), %rcx
	leaq	232(%rsp), %rdx
	call	L__copy_gf$1
L__gf_inv$10:
	leaq	104(%rsp), %rcx
	leaq	200(%rsp), %rdx
	call	L__copy_gf$1
L__gf_inv$9:
	leaq	136(%rsp), %rcx
	leaq	168(%rsp), %rdx
	call	L__copy_gf$1
L__gf_inv$8:
	movq	16(%rsp), %rax
	incq	%rax
L__gf_inv$6:
	cmpq	$15, %rax
	jb  	L__gf_inv$7
	movq	72(%rsp), %rbp
	movq	40(%rsp), %r13
	call	L__asm_volatile2$1
L__gf_inv$5:
	leaq	40(%rsp), %r8
	leaq	104(%rsp), %rdx
	leaq	136(%rsp), %rax
	movq	%rcx, %rdi
	movq	%rsi, %rcx
	leaq	-80(%rsp), %rsp
	call	L__gf_lin$1
L__gf_inv$4:
	leaq	80(%rsp), %rsp
	movq	8(%rsp), %rcx
	leaq	40(%rsp), %rsi
	leaq	glob_data + 0(%rip), %rdi
	leaq	-24(%rsp), %rsp
	call	L__gf_mul$1
L__gf_inv$3:
	leaq	24(%rsp), %rsp
	call	L__gf_iszero$1
L__gf_inv$2:
	ret
L__asm_volatile2$1:
	movq	$1, %rdi
	xorq	%r9, %r9
	xorq	%rcx, %rcx
	movq	$1, %rsi
	movq	$20, %rax
	cmpq	$0, %rax
	jmp 	L__asm_volatile2$3
L__asm_volatile2$4:
	call	Linv_inner$1
L__asm_volatile2$6:
	call	Linv_inner$1
L__asm_volatile2$5:
	decq	%rax
	cmpq	$0, %rax
L__asm_volatile2$3:
	jns 	L__asm_volatile2$4
	call	Linv_inner$1
L__asm_volatile2$2:
	ret
L__asm_volatile$1:
	movq	$9223372034707292159, %rdx
	movq	$9223372034707292160, %rdi
	movq	$-9223372034707292161, %r11
	movq	$30, %rsi
	cmpq	$0, %rsi
	jmp 	L__asm_volatile$2
L__asm_volatile$3:
	call	Linv_inner_fast$1
L__asm_volatile$4:
	decq	%rsi
	cmpq	$0, %rsi
L__asm_volatile$2:
	jns 	L__asm_volatile$3
	movq	%rdi, %r12
	movq	%r11, %rcx
	shrq	$32, %r12
	shrq	$32, %rcx
	movq	$4294967295, %rax
	andq	%rax, %rdi
	movq	$4294967295, %rax
	andq	%rax, %r11
	subq	$2147483647, %rdi
	subq	$2147483647, %r12
	subq	$2147483647, %r11
	subq	$2147483647, %rcx
	ret
Linv_inner_fast$1:
	movq	%rdi, %r8
	movq	%r11, %r9
	movq	%rax, %r10
	movq	%rcx, %rbx
	cmpq	%rax, %rcx
	cmovnb	%rbx, %rax
	cmovnb	%r10, %rcx
	cmovnb	%r9, %rdi
	cmovnb	%r8, %r11
	subq	%rcx, %rax
	subq	%r11, %rdi
	addq	%rdx, %rdi
	movq	$1, %rbp
	testq	%r10, %rbp
	cmovp	%r8, %rdi
	cmovp	%r9, %r11
	cmovp	%r10, %rax
	cmovp	%rbx, %rcx
	shrq	$1, %rax
	addq	%r11, %r11
	subq	%rdx, %r11
	ret
Linv_inner$1:
	movq	%rdi, %rdx
	movq	%r9, %r8
	movq	%rcx, %r10
	movq	%rsi, %r11
	movq	%rbp, %rbx
	movq	%r13, %r12
	cmpq	%rbx, %r12
	cmovnb	%r12, %rbp
	cmovnb	%rbx, %r13
	cmovnb	%r10, %rdi
	cmovnb	%rdx, %rcx
	cmovnb	%r11, %r9
	cmovnb	%r8, %rsi
	subq	%r13, %rbp
	subq	%rcx, %rdi
	subq	%rsi, %r9
	movq	%rbx, %r14
	movq	$1, %r15
	testq	%r15, %r14
	cmovp	%rdx, %rdi
	cmovp	%r8, %r9
	cmovp	%r10, %rcx
	cmovp	%r11, %rsi
	cmovp	%rbx, %rbp
	cmovp	%r12, %r13
	shrq	$1, %rbp
	addq	%rcx, %rcx
	addq	%rsi, %rsi
	ret
L__gf_lin$1:
	movq	%r8, 8(%rsp)
	movq	%rdi, %r8
	shrq	$63, %r8
	movq	%r8, %rsi
	negq	%rsi
	xorq	%rsi, %rdi
	addq	%r8, %rdi
	movq	%rcx, %rsi
	shrq	$63, %rsi
	movq	%rsi, %r9
	negq	%r9
	xorq	%r9, %rcx
	addq	%rsi, %rcx
	movq	%rsi, 16(%rsp)
	leaq	24(%rsp), %rsi
	movq	%rdx, %r9
	movq	%r8, %rdx
	leaq	-32(%rsp), %rsp
	call	L__gf_condneg$1
L__gf_lin$3:
	leaq	32(%rsp), %rsp
	movq	16(%rsp), %rdx
	leaq	56(%rsp), %rsi
	movq	%rax, %r9
	leaq	-32(%rsp), %rsp
	call	L__gf_condneg$1
L__gf_lin$2:
	leaq	32(%rsp), %rsp
	movq	24(%rsp), %rax
	movq	%rdi, %rdx
	mulq	%rdx
	movq	%rax, %rsi
	movq	%rdx, %r9
	movq	56(%rsp), %rax
	movq	%rcx, %rdx
	mulq	%rdx
	xorq	%r8, %r8
	adcxq	%rax, %rsi
	movq	%rsi, %r8
	adcxq	%rdx, %r9
	movq	32(%rsp), %rax
	movq	%rdi, %rdx
	mulq	%rdx
	xorq	%rsi, %rsi
	adcxq	%r9, %rax
	movq	$0, %rsi
	adcxq	%rsi, %rdx
	movq	%rdx, %r9
	movq	%rax, %rsi
	movq	64(%rsp), %rax
	movq	%rcx, %rdx
	mulq	%rdx
	xorq	%r10, %r10
	adcxq	%rax, %rsi
	adcxq	%rdx, %r9
	movq	40(%rsp), %rax
	movq	%rdi, %rdx
	mulq	%rdx
	xorq	%r10, %r10
	adcxq	%r9, %rax
	movq	$0, %r9
	adcxq	%r9, %rdx
	movq	%rdx, %r10
	movq	%rax, %r9
	movq	72(%rsp), %rax
	movq	%rcx, %rdx
	mulq	%rdx
	xorq	%r11, %r11
	adcxq	%rax, %r9
	adcxq	%rdx, %r10
	movq	48(%rsp), %rax
	mulq	%rdi
	xorq	%rdi, %rdi
	adcxq	%r10, %rax
	movq	$0, %rdi
	adcxq	%rdi, %rdx
	movq	%rdx, %rdi
	movq	%rax, %r10
	movq	80(%rsp), %rax
	mulq	%rcx
	xorq	%rcx, %rcx
	adcxq	%rax, %r10
	movq	%r10, %rcx
	adcxq	%rdx, %rdi
	movq	$38, %rax
	mulq	%rdi
	xorq	%rdi, %rdi
	adcxq	%r8, %rax
	adcxq	%rsi, %rdx
	movq	$0, %rsi
	adcxq	%r9, %rsi
	movq	$0, %rdi
	adcxq	%rcx, %rdi
	movq	$0, %rcx
	movq	$-1, %r8
	cmovb	%r8, %rcx
	movq	$38, %r8
	andq	%r8, %rcx
	xorq	%r8, %r8
	adcxq	%rax, %rcx
	movq	$0, %rax
	adcxq	%rdx, %rax
	movq	8(%rsp), %rdx
	movq	%rcx, (%rdx)
	movq	%rax, 8(%rdx)
	movq	%rsi, 16(%rdx)
	movq	%rdi, 24(%rdx)
	ret
L__gf_condneg$1:
	leaq	8(%rsp), %r8
	call	L__gf_neg$1
L__gf_condneg$2:
	movq	8(%rsp), %r8
	movq	(%r9), %r10
	xorq	%r10, %r8
	movq	%rdx, %r10
	negq	%r10
	andq	%r10, %r8
	movq	(%r9), %r10
	xorq	%r10, %r8
	movq	%r8, (%rsi)
	movq	16(%rsp), %r8
	movq	8(%r9), %r10
	xorq	%r10, %r8
	movq	%rdx, %r10
	negq	%r10
	andq	%r10, %r8
	movq	8(%r9), %r10
	xorq	%r10, %r8
	movq	%r8, 8(%rsi)
	movq	24(%rsp), %r8
	movq	16(%r9), %r10
	xorq	%r10, %r8
	movq	%rdx, %r10
	negq	%r10
	andq	%r10, %r8
	movq	16(%r9), %r10
	xorq	%r10, %r8
	movq	%r8, 16(%rsi)
	movq	32(%rsp), %r8
	movq	24(%r9), %r10
	xorq	%r10, %r8
	negq	%rdx
	andq	%rdx, %r8
	movq	24(%r9), %rdx
	xorq	%rdx, %r8
	movq	%r8, 24(%rsi)
	ret
L__gf_neg$1:
	movq	$38, %r10
	negq	%r10
	movq	(%r9), %r11
	xorq	%rbx, %rbx
	sbbq	%r11, %r10
	movq	$-1, %r11
	movq	8(%r9), %rbx
	sbbq	%rbx, %r11
	movq	$-1, %rbx
	movq	16(%r9), %rbp
	sbbq	%rbp, %rbx
	movq	$-1, %rbp
	movq	24(%r9), %r12
	sbbq	%r12, %rbp
	movq	$0, %r12
	movq	$-1, %r13
	cmovb	%r13, %r12
	movq	%r12, %r13
	shrq	$1, %r13
	movq	%r12, %r14
	andq	$-19, %r14
	xorq	%r15, %r15
	adcxq	%r10, %r14
	movq	%r14, (%r8)
	movq	%r12, %r10
	adcxq	%r11, %r10
	movq	%r10, 8(%r8)
	adcxq	%rbx, %r12
	movq	%r12, 16(%r8)
	adcxq	%rbp, %r13
	movq	%r13, 24(%r8)
	ret
L__s256_lin_div31_abs$1:
	movq	%rsi, %r9
	shrq	$63, %r9
	movq	%r9, %r10
	negq	%r9
	xorq	%rsi, %r9
	addq	%r10, %r9
	movq	%r10, %rsi
	movq	%r8, %r10
	shrq	$63, %r10
	movq	%r10, %rbx
	negq	%r10
	xorq	%r8, %r10
	addq	%rbx, %r10
	movq	%rbx, %r8
	movq	%rsi, %rbx
	negq	%rsi
	movq	(%rax), %r13
	xorq	%rsi, %r13
	movq	%r13, 72(%rsp)
	movq	8(%rax), %r13
	xorq	%rsi, %r13
	movq	%r13, 80(%rsp)
	movq	16(%rax), %r13
	xorq	%rsi, %r13
	movq	%r13, 88(%rsp)
	movq	24(%rax), %rax
	xorq	%rsi, %rax
	movq	%rax, 96(%rsp)
	xorq	%rax, %rax
	movq	72(%rsp), %rax
	adcxq	%rbx, %rax
	movq	%rax, 8(%rsp)
	movq	80(%rsp), %rax
	movq	$0, %rsi
	adcxq	%rsi, %rax
	movq	%rax, 16(%rsp)
	movq	88(%rsp), %rax
	adcxq	%rsi, %rax
	movq	%rax, 24(%rsp)
	movq	96(%rsp), %rax
	adcxq	%rsi, %rax
	movq	%rax, 32(%rsp)
	movq	%r8, %rax
	negq	%r8
	movq	(%rdx), %rsi
	xorq	%r8, %rsi
	movq	%rsi, 72(%rsp)
	movq	8(%rdx), %rsi
	xorq	%r8, %rsi
	movq	%rsi, 80(%rsp)
	movq	16(%rdx), %rsi
	xorq	%r8, %rsi
	movq	%rsi, 88(%rsp)
	movq	24(%rdx), %rdx
	xorq	%r8, %rdx
	movq	%rdx, 96(%rsp)
	xorq	%rdx, %rdx
	movq	72(%rsp), %rdx
	adcxq	%rax, %rdx
	movq	%rdx, 40(%rsp)
	movq	80(%rsp), %rax
	movq	$0, %rdx
	adcxq	%rdx, %rax
	movq	%rax, 48(%rsp)
	movq	88(%rsp), %rax
	adcxq	%rdx, %rax
	movq	%rax, 56(%rsp)
	movq	96(%rsp), %rax
	adcxq	%rdx, %rax
	movq	%rax, 64(%rsp)
	movq	8(%rsp), %rax
	movq	%r9, %rdx
	mulq	%rdx
	movq	%rdx, %rsi
	movq	%rax, %r8
	movq	40(%rsp), %rax
	movq	%r10, %rdx
	mulq	%rdx
	xorq	%rbx, %rbx
	adcxq	%rax, %r8
	adcxq	%rdx, %rsi
	movq	16(%rsp), %rax
	movq	%r9, %rdx
	mulq	%rdx
	xorq	%rbx, %rbx
	adcxq	%rsi, %rax
	movq	$0, %rsi
	adcxq	%rsi, %rdx
	movq	%rdx, %rbx
	movq	%rax, %rsi
	movq	48(%rsp), %rax
	movq	%r10, %rdx
	mulq	%rdx
	xorq	%r13, %r13
	adcxq	%rax, %rsi
	adcxq	%rdx, %rbx
	movq	24(%rsp), %rax
	movq	%r9, %rdx
	mulq	%rdx
	xorq	%r13, %r13
	adcxq	%rbx, %rax
	movq	%rax, %rbx
	movq	$0, %rax
	adcxq	%rax, %rdx
	movq	%rdx, %r13
	movq	56(%rsp), %rax
	movq	%r10, %rdx
	mulq	%rdx
	xorq	%r14, %r14
	adcxq	%rax, %rbx
	adcxq	%rdx, %r13
	movq	32(%rsp), %rax
	movq	%r9, %rdx
	mulq	%rdx
	xorq	%r14, %r14
	adcxq	%r13, %rax
	movq	%rax, %r14
	movq	$0, %rax
	adcxq	%rax, %rdx
	movq	%rdx, %r13
	movq	64(%rsp), %rax
	movq	%r10, %rdx
	mulq	%rdx
	xorq	%r15, %r15
	adcxq	%rax, %r14
	movq	%r14, %rax
	adcxq	%rdx, %r13
	movq	%r13, %rdx
	movq	32(%rsp), %r13
	shrq	$63, %r13
	negq	%r13
	andq	%r9, %r13
	subq	%r13, %rdx
	movq	64(%rsp), %r9
	shrq	$63, %r9
	negq	%r9
	andq	%r10, %r9
	subq	%r9, %rdx
	movq	%r8, %r9
	shrq	$31, %r9
	movq	%rsi, %r8
	shlq	$33, %r8
	orq 	%r9, %r8
	movq	%rsi, %r9
	shrq	$31, %r9
	movq	%rbx, %rsi
	shlq	$33, %rsi
	orq 	%r9, %rsi
	shrq	$31, %rbx
	movq	%rax, %r9
	shlq	$33, %r9
	orq 	%rbx, %r9
	movq	%rax, %r10
	shrq	$31, %r10
	movq	%rdx, %rax
	shlq	$33, %rax
	orq 	%r10, %rax
	shrq	$63, %rdx
	movq	%rdx, %r10
	negq	%rdx
	xorq	%rdx, %r8
	xorq	%rdx, %rsi
	xorq	%rdx, %r9
	xorq	%rdx, %rax
	xorq	%rbx, %rbx
	adcxq	%r10, %r8
	movq	%r8, (%rbp)
	movq	$0, %r8
	adcxq	%r8, %rsi
	movq	%rsi, 8(%rbp)
	adcxq	%r8, %r9
	movq	%r9, 16(%rbp)
	adcxq	%r8, %rax
	movq	%rax, 24(%rbp)
	ret
L__gf_normalize$1:
	movq	24(%rdi), %rdx
	shrq	$63, %rdx
	negq	%rdx
	movq	%rdx, %r8
	shlq	$63, %r8
	movq	(%rdi), %r9
	movq	%rdx, %rsi
	andq	$19, %rsi
	xorq	%r10, %r10
	adcxq	%rsi, %r9
	movq	8(%rdi), %r10
	movq	$0, %r11
	adcxq	%r11, %r10
	movq	16(%rdi), %rsi
	adcxq	%r11, %rsi
	movq	24(%rdi), %r11
	adcxq	%r8, %r11
	movq	$-1, %r8
	shrq	$1, %r8
	xorq	%rdi, %rdi
	movq	%r9, %rdi
	movq	$-19, %r9
	sbbq	%r9, %rdi
	movq	$-1, %r9
	sbbq	%r9, %r10
	sbbq	%r9, %rsi
	sbbq	%r8, %r11
	sbbq	$0, %rdx
	movq	%rdx, %r8
	shrq	$1, %r8
	movq	$-19, %r9
	andq	%rdx, %r9
	xorq	%rbx, %rbx
	adcxq	%r9, %rdi
	movq	%rdi, (%rcx)
	adcxq	%rdx, %r10
	movq	%r10, 8(%rcx)
	adcxq	%rdx, %rsi
	movq	%rsi, 16(%rcx)
	adcxq	%r8, %r11
	movq	%r11, 24(%rcx)
	ret
L__copy_gf$1:
	movq	(%rdx), %rsi
	movq	%rsi, (%rcx)
	movq	8(%rdx), %rsi
	movq	%rsi, 8(%rcx)
	movq	16(%rdx), %rsi
	movq	%rsi, 16(%rcx)
	movq	24(%rdx), %rdx
	movq	%rdx, 24(%rcx)
	ret
L__gf_mul$1:
	movq	%rcx, 8(%rsp)
	xorq	%rax, %rax
	movq	(%rsi), %rdx
	movq	%rsi, 16(%rsp)
	movq	(%rdi), %rcx
	movq	%rdi, 24(%rsp)
	mulxq	%rcx, %rsi, %rcx
	movq	24(%rsp), %rdi
	movq	8(%rdi), %r8
	movq	%rdi, 24(%rsp)
	mulxq	%r8, %r8, %rdi
	adoxq	%r8, %rcx
	movq	24(%rsp), %r8
	movq	16(%r8), %r9
	movq	%r8, 24(%rsp)
	mulxq	%r9, %r9, %r8
	adoxq	%r9, %rdi
	movq	24(%rsp), %r9
	movq	24(%r9), %r10
	movq	%r9, 24(%rsp)
	mulxq	%r10, %rdx, %r9
	adoxq	%rdx, %r8
	adoxq	%rax, %r9
	movq	16(%rsp), %r10
	movq	8(%r10), %rdx
	movq	%r10, 16(%rsp)
	movq	24(%rsp), %r10
	movq	(%r10), %r11
	movq	%r10, 24(%rsp)
	mulxq	%r11, %r11, %r10
	adcxq	%r11, %rcx
	adoxq	%r10, %rdi
	movq	24(%rsp), %r10
	movq	8(%r10), %r11
	movq	%r10, 24(%rsp)
	mulxq	%r11, %r11, %r10
	adcxq	%r11, %rdi
	adoxq	%r10, %r8
	movq	24(%rsp), %r10
	movq	16(%r10), %r11
	movq	%r10, 24(%rsp)
	mulxq	%r11, %r11, %r10
	adcxq	%r11, %r8
	adoxq	%r10, %r9
	movq	24(%rsp), %r10
	movq	24(%r10), %r11
	movq	%r10, 24(%rsp)
	mulxq	%r11, %rdx, %r10
	adcxq	%rdx, %r9
	adoxq	%rax, %r10
	adcxq	%rax, %r10
	movq	16(%rsp), %r11
	movq	16(%r11), %rdx
	movq	%r11, 16(%rsp)
	movq	24(%rsp), %r11
	movq	(%r11), %rbx
	movq	%r11, 24(%rsp)
	mulxq	%rbx, %rbx, %r11
	adcxq	%rbx, %rdi
	adoxq	%r11, %r8
	movq	24(%rsp), %r11
	movq	8(%r11), %rbx
	movq	%r11, 24(%rsp)
	mulxq	%rbx, %rbx, %r11
	adcxq	%rbx, %r8
	adoxq	%r11, %r9
	movq	24(%rsp), %r11
	movq	16(%r11), %rbx
	movq	%r11, 24(%rsp)
	mulxq	%rbx, %rbx, %r11
	adcxq	%rbx, %r9
	adoxq	%r11, %r10
	movq	24(%rsp), %r11
	movq	24(%r11), %rbx
	movq	%r11, 24(%rsp)
	mulxq	%rbx, %rdx, %r11
	adcxq	%rdx, %r10
	adoxq	%rax, %r11
	adcxq	%rax, %r11
	movq	16(%rsp), %rax
	movq	24(%rax), %rdx
	movq	$0, %rbx
	movq	24(%rsp), %rax
	movq	(%rax), %rbp
	movq	%rax, 24(%rsp)
	mulxq	%rbp, %rbp, %rax
	adcxq	%rbp, %r8
	adoxq	%rax, %r9
	movq	24(%rsp), %rax
	movq	8(%rax), %rbp
	movq	%rax, 24(%rsp)
	mulxq	%rbp, %rbp, %rax
	adcxq	%rbp, %r9
	adoxq	%rax, %r10
	movq	24(%rsp), %rax
	movq	16(%rax), %rbp
	movq	%rax, 24(%rsp)
	mulxq	%rbp, %rbp, %rax
	adcxq	%rbp, %r10
	adoxq	%rax, %r11
	movq	24(%rsp), %rax
	movq	24(%rax), %rax
	mulxq	%rax, %rdx, %rax
	adcxq	%rdx, %r11
	adoxq	%rbx, %rax
	adcxq	%rbx, %rax
	movq	$38, %rdx
	mulxq	%r9, %rbp, %r9
	adcxq	%rbp, %rsi
	adoxq	%r9, %rcx
	mulxq	%r10, %r10, %r9
	adcxq	%r10, %rcx
	adoxq	%r9, %rdi
	mulxq	%r11, %r10, %r9
	adcxq	%r10, %rdi
	adoxq	%r9, %r8
	mulxq	%rax, %rax, %rdx
	adcxq	%rax, %r8
	adoxq	%rbx, %rdx
	adcxq	%rbx, %rdx
	shldq	$1, %r8, %rdx
	movq	$9223372036854775807, %rax
	andq	%rax, %r8
	movq	$19, %rax
	imulq	%rdx
	addq	%rax, %rsi
	addq	%rbx, %rcx
	addq	%rbx, %rdi
	addq	%rbx, %r8
	movq	8(%rsp), %rax
	movq	%rsi, (%rax)
	movq	%rcx, 8(%rax)
	movq	%rdi, 16(%rax)
	movq	%r8, 24(%rax)
	ret
L__gf_iszero$1:
	movq	(%rax), %rcx
	orq 	8(%rax), %rcx
	orq 	16(%rax), %rcx
	orq 	24(%rax), %rcx
	movq	(%rax), %rdx
	addq	$19, %rdx
	movq	8(%rax), %rsi
	xorq	$-1, %rsi
	orq 	%rsi, %rdx
	movq	16(%rax), %rsi
	xorq	$-1, %rsi
	orq 	%rsi, %rdx
	movq	24(%rax), %rsi
	movq	$9223372036854775807, %rdi
	xorq	%rdi, %rsi
	orq 	%rsi, %rdx
	movq	(%rax), %rsi
	addq	$38, %rsi
	movq	8(%rax), %rdi
	xorq	$-1, %rdi
	orq 	%rdi, %rsi
	movq	16(%rax), %rdi
	xorq	$-1, %rdi
	orq 	%rdi, %rsi
	movq	24(%rax), %rax
	xorq	$-1, %rax
	orq 	%rax, %rsi
	movq	$0, %rax
	subq	%rcx, %rax
	orq 	%rax, %rcx
	movq	$0, %rax
	subq	%rdx, %rax
	orq 	%rax, %rdx
	movq	$0, %rax
	subq	%rsi, %rax
	orq 	%rax, %rsi
	andq	%rdx, %rcx
	andq	%rsi, %rcx
	shrq	$63, %rcx
	movq	$1, %rax
	subq	%rcx, %rax
	ret
	.data
	.p2align	5
_glob_data:
glob_data:
      .byte 108
      .byte 96
      .byte -72
      .byte -100
      .byte -85
      .byte -34
      .byte -42
      .byte 41
      .byte -3
      .byte 99
      .byte 123
      .byte -126
      .byte 8
      .byte -44
      .byte -115
      .byte 120
      .byte -26
      .byte -125
      .byte 86
      .byte -106
      .byte 76
      .byte 116
      .byte -4
      .byte 60
      .byte 26
      .byte -93
      .byte 10
      .byte 73
      .byte -79
      .byte 22
      .byte -32
      .byte 36
      .byte -19
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte -1
      .byte 127
      .byte 1
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
