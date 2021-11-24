	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$8, %rsp
	movq	$0, %rsi
	movq	$42, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	