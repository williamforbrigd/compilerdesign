	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	$1, %rsi
	andq	$0, %rsi
	movq	%rsi, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	