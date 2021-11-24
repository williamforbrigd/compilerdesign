	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	$9, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	
	.text
main.end:
	movq	$9, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	