	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	$0, %rsi
	xorq	$0, %rsi
	movq	%rsi, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	