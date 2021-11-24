	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	$3, %rsi
	cmpq	$0, %rsi
	movq	$9, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	
	.text
main.then:
	movq	$7, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	
	.text
main.else:
	movq	$9, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	