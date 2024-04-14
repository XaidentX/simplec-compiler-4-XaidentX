.file "stdin"
.text
.globl main
.type main, @function
main:
	# stack space for argc and argv
	# emit main's prologue
	push	%rbp
	mov	%rsp, %rbp
	sub	$24, %rsp
	push	%rbx
	# move argc and argv from parameter registers to the stack
	mov	%rdi, -16(%rbp)
	mov	%rsi, -24(%rbp)
	# generate code for the body
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$3, %rax
	push	%rax
	pop	%rax
	mov	%rax, -8(%rbp)
	# generating code for a whilestmt
	# emit the head label
.L0:
	# generate code for the expression
	mov	-8(%rbp), %rax
	push	%rax
	# emit a pop of the expression value from the stack into a register
	pop	%rax
	# emit a cmp of register's value to 0, i.e., check whether it's false
	cmp $0, %rax
	# emit a je to the end label
	je .L1
	# generate code for the if branch
	# generate code for the right-hand side of the assignment
	# generate code for the left operand
	mov	-8(%rbp), %rax
	push	%rax
	# generate code for the right operand
	# push the integer
	mov	$1, %rax
	push	%rax
	# pop the right operand
	pop	%rbx
	# pop the left operand
	pop	%rax
	# do the subtraction
	sub	%rbx, %rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -8(%rbp)
	# emit a jump to the head label
	jmp .L0
	# emit the end label
.L1:
	# generate code for the return expression
	mov	-8(%rbp), %rax
	push	%rax
	# save the return expression into %rax per the abi
	pop	%rax
	# emit main's epilogue
	pop	%rbx
	mov	%rbp, %rsp
	pop	%rbp
	ret
