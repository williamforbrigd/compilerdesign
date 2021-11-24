	.data
	.globl	_gstr
_gstr:
	.asciz	"hello, world!"
	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	%rsi, %rsi
	movq	%rsi, %rdi
	callq	ll_strcat
	movq	%rax, %rdx
	movq	%rdx, %rdi
	callq	ll_puts
	movq	%rax, %rcx
	movq	$0, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	