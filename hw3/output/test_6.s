	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	$42, %rsi
	shlq	$2, %rsi
	movq	%rsi, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	