	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$8, %rsp
	movq	$17, %rsi
	subq	$8, %rsp
	movq	%rsi, %rcx
	movq	$17, -16(%rsp)
	subq	$-16, %rsp
	movq	16(%rbp), %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	