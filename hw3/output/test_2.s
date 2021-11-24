	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	$5, %rsi
	movq	%rsi, %r8 
	imulq	$9, %r8 
	movq	%r8 , %rsi
	movq	%rsi, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	