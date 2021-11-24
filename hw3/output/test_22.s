	.data
	.globl	_tmp
_tmp:
	.quad	1
	.quad	2
	.quad	3
	.quad	4
	.quad	5
	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$8, %rsp
	movq	$17, -16(%rsp)
	subq	$-16, %rsp
	movq	%rcx, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	