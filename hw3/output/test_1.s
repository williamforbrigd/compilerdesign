	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	$10, %rsi
	subq	$9, %rsi
	movq	%rsi, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	