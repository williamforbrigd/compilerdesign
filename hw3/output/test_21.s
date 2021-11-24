	.data
	.globl	_gint
_gint:
	.quad	42
	.data
	.globl	_v1
_v1:
	.quad	0
	.quad	_gint
	.data
	.globl	_v2
_v2:
	.quad	1
	.quad	0
	.data
	.globl	_gstr
_gstr:
	.asciz	"hello, world!"
	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	subq	$8, %rsp
	movq	$5, %rdx
	movq	%r8 , %rdi
	callq	foo
	movq	%rax, %r9 
	movq	$17, -16(%rsp)
	subq	$-16, %rsp
	movq	16(%rbp), %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	
	.text
	.globl	foo
foo:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	$6, %rsi
	movq	$17, -16(%rsp)
	subq	$-16, %rsp
	retq	