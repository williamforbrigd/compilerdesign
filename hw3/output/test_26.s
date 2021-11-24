	.data
	.globl	_gbl
_gbl:
	.quad	1
	.quad	2
	.quad	3
	.quad	4
	.quad	5
	.quad	6
	.quad	7
	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	$17, -16(%rsp)
	subq	$-16, %rsp
	movq	%rdx, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	