	.data
	.globl	_gstr
_gstr:
	.asciz	"hello, world!"
	.text
	.globl	main
main:
	pushq	%rbp
	movq	%rsp, %rbp
	movq	%rsi, %rdi
	callq	ll_puts
	movq	%rax, %rdx
	movq	$0, %rax
	movq	%rbp, %rsp
	popq	%rbp
	retq	