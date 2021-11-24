	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$8, %rsp
	movq	$17, %rsi
	movq	$17, -16(%rsp)
	subq	$-16, %rsp
	movq	%rcx, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	