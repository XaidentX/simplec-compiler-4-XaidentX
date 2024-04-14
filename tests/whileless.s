.file "stdin"
.text
.globl main
.type main, @function
main:
	# stack space for argc and argv
	# emit main's prologue
	push	%rbp
	mov	%rsp, %rbp
	sub	$40, %rsp
	push	%rbx
	# move argc and argv from parameter registers to the stack
	mov	%rdi, -32(%rbp)
	mov	%rsi, -40(%rbp)
	# generate code for the body
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$2, %rax
	push	%rax
	pop	%rax
	mov	%rax, -8(%rbp)
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$1, %rax
	push	%rax
	pop	%rax
	mov	%rax, -16(%rbp)
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$0, %rax
	push	%rax
	pop	%rax
	mov	%rax, -24(%rbp)
	# generating code for a whilestmt
	# emit the head label
.L0:
	# generate code for the expression
	mov	-16(%rbp), %rax
	push	%rax
	# emit a pop of the expression value from the stack into a register
	pop	%rax
	# emit a cmp of register's value to 0, i.e., check whether it's false
	cmp $0, %rax
	# emit a je to the end label
	je .L1
	# generate code for the if branch
	# generating code for an ifstmt
	# generate code for the expression
	# generate code for the left operand
	mov	-24(%rbp), %rax
	push	%rax
	# generate code for the right operand
	# push the integer
	mov	$1, %rax
	push	%rax
	# pop the right operand
	pop	%rbx
	# pop the left operand
	pop	%rax
	cmp	%rax, %rbx
	jle	.L2
	mov	$1, %rax
	jmp	.L3
.L2:
	mov	$0, %rax
.L3:
	push	%rax
	# push the expression result
	push	%rax
	# emit a pop of the expression value from the stack into a register
	pop	%rax
	# emit a cmp of register's value to 0, i.e., check whether it's false
	cmp $0, %rax
	# emit a je to the end label
	je .L4
	# generate code for the if branch
	# generate code for the right-hand side of the assignment
	# generate code for the left operand
	mov	-8(%rbp), %rax
	push	%rax
	# generate code for the right operand
	mov	-16(%rbp), %rax
	push	%rax
	# pop the right operand
	pop	%rbx
	# pop the left operand
	pop	%rax
	# do the addition
	add	%rbx, %rax
	push	%rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -8(%rbp)
	# emit the end label
.L4:
	# generating code for an ifstmt
	# generate code for the expression
	# generate code for the left operand
	# push the integer
	mov	$1, %rax
	push	%rax
	# generate code for the right operand
	# push the integer
	mov	$2, %rax
	push	%rax
	# pop the right operand
	pop	%rbx
	# pop the left operand
	pop	%rax
	cmp	%rax, %rbx
	jle	.L5
	mov	$1, %rax
	jmp	.L6
.L5:
	mov	$0, %rax
.L6:
	push	%rax
	# push the expression result
	push	%rax
	# emit a pop of the expression value from the stack into a register
	pop	%rax
	# emit a cmp of register's value to 0, i.e., check whether it's false
	cmp $0, %rax
	# emit a je to the end label
	je .L7
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
	push	%rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -8(%rbp)
	# emit the end label
.L7:
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$3, %rax
	push	%rax
	pop	%rax
	mov	%rax, -24(%rbp)
	# generating code for an ifstmt
	# generate code for the expression
	# generate code for the left operand
	mov	-24(%rbp), %rax
	push	%rax
	# generate code for the right operand
	# push the integer
	mov	$2, %rax
	push	%rax
	# pop the right operand
	pop	%rbx
	# pop the left operand
	pop	%rax
	cmp	%rax, %rbx
	jle	.L8
	mov	$1, %rax
	jmp	.L9
.L8:
	mov	$0, %rax
.L9:
	push	%rax
	# push the expression result
	push	%rax
	# emit a pop of the expression value from the stack into a register
	pop	%rax
	# emit a cmp of register's value to 0, i.e., check whether it's false
	cmp $0, %rax
	# emit a je to the end label
	je .L10
	# generate code for the if branch
	# generate code for the right-hand side of the assignment
	mov	-24(%rbp), %rax
	push	%rax
	pop	%rax
	mov	%rax, -8(%rbp)
	# emit the end label
.L10:
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$0, %rax
	push	%rax
	pop	%rax
	mov	%rax, -16(%rbp)
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
