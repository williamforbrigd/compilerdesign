	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	$5, %rsi
	addq	$12, %rsi
	movq	$9, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	
	.text
main.next:
	movq	$9, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	
	.text
main.end:
	movq	%rsi, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	