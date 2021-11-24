	.text
	.globl	foo
foo:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	$42, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	
	.text
	.globl	bar
bar:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	$0, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	
	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$8, %rsp
	subq	$8, %rsp
	movq	$0, %rsi
	movq	$100, %rdx
	movq	$17, -16(%rsp)
	subq	$-16, %rsp
	movq	%r9 , 16(%rbp)
	cmpq	$0, 16(%rbp)
	movq	$9, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	
	.text
main.then:
	callq	foo
	movq	%rax, 24(%rbp)
	movq	24(%rbp), %rsi
	movq	$9, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	
	.text
main.else:
	callq	bar
	movq	%rax, 40(%rbp)
	movq	40(%rbp), %rsi
	movq	$9, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	
	.text
main.end:
	movq	$17, -16(%rsp)
	subq	$-16, %rsp
	movq	56(%rbp), %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	