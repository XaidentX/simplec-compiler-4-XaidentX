.file "stdin"
.text
.globl main
.type main, @function
main:
	# stack space for argc and argv
	# emit main's prologue
	push	%rbp
	mov	%rsp, %rbp
	sub	$48, %rsp
	push	%rbx
	# move argc and argv from parameter registers to the stack
	mov	%rdi, -40(%rbp)
	mov	%rsi, -48(%rbp)
	# generate code for the body
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$1, %rax
	push	%rax
	pop	%rax
	mov	%rax, -8(%rbp)
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$2, %rax
	push	%rax
	pop	%rax
	mov	%rax, -16(%rbp)
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$5, %rax
	push	%rax
	pop	%rax
	mov	%rax, -24(%rbp)
	# generating code for a whilestmt
	# emit the head label
.L0:
	# generate code for the expression
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
	# push the integer
	mov	$1, %rax
	push	%rax
	# generate code for the right operand
	# push the integer
	mov	$1, %rax
	push	%rax
	# pop the right operand
	pop	%rbx
	# pop the left operand
	pop	%rax
	# conjuction &&
	cmp $0, %rax
	je .L2
	cmp $0, %rbx
	je .L2
	mov	$1, %rax
	jmp .L3
.L2:
	mov	$0, %rax
.L3:
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
	# copy the base pointer to another register
	mov	%rbp, %rax
	# subtract the offset from the copy of the base pointer
	sub	$24, %rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -32(%rbp)
	# generate code for the deref on the left side of an expression
	mov	-32(%rbp), %rax
	push	%rax
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$42, %rax
	push	%rax
	# pop the result of the right-hand side
	pop	%rax
	# pop the result of the left-hand side
	pop	%rbx
	# move the right-hand side's value into the address pointed to by the left-hand size
	mov	%rax, (%rbx)
	# generate code for the right-hand side of the assignment
	# generate code for the left operand
	# generate code for the unary operand
	mov	-32(%rbp), %rax
	push	%rax
	# pop the unary operand
	pop	%rax
	# move the contents of the address to the result register
	mov	(%rax), %rbx
	# push the expression result
	push	%rbx
	# generate code for the right operand
	# push the integer
	mov	$1, %rax
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
	mov	%rax, -24(%rbp)
	# emit the end label
.L4:
	# generating code for an ifstmt
	# generate code for the expression
	# generate code for the left operand
	# push the integer
	mov	$0, %rax
	push	%rax
	# generate code for the right operand
	# push the integer
	mov	$1, %rax
	push	%rax
	# pop the right operand
	pop	%rbx
	# pop the left operand
	pop	%rax
	# disjuction ||
	cmp $0, %rax
	jne .L5
	cmp $0, %rbx
	jne .L5
	mov	$0, %rax
	jmp .L6
.L5:
	mov	$1, %rax
.L6:
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
	# copy the base pointer to another register
	mov	%rbp, %rax
	# subtract the offset from the copy of the base pointer
	sub	$16, %rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -32(%rbp)
	# generate code for the deref on the left side of an expression
	mov	-32(%rbp), %rax
	push	%rax
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$24, %rax
	push	%rax
	# pop the result of the right-hand side
	pop	%rax
	# pop the result of the left-hand side
	pop	%rbx
	# move the right-hand side's value into the address pointed to by the left-hand size
	mov	%rax, (%rbx)
	# generate code for the right-hand side of the assignment
	# generate code for the left operand
	# generate code for the unary operand
	mov	-32(%rbp), %rax
	push	%rax
	# pop the unary operand
	pop	%rax
	# move the contents of the address to the result register
	mov	(%rax), %rbx
	# push the expression result
	push	%rbx
	# generate code for the right operand
	# push the integer
	mov	$1, %rax
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
	mov	%rax, -16(%rbp)
	# emit the end label
.L7:
	# generating code for an ifelsestmt
	# generate code for the expression
	# generate code for the left operand
	# push the integer
	mov	$0, %rax
	push	%rax
	# generate code for the right operand
	# push the integer
	mov	$1, %rax
	push	%rax
	# pop the right operand
	pop	%rbx
	# pop the left operand
	pop	%rax
	# push the expression result
	push	%rax
	# emit a pop of the expression value from the stack into a register
	pop	%rax
	# emit a cmp of register's value to 0, i.e., check whether it's false
	cmp $0, %rax
	# emit a je to the else label
	je .L8
	# generate code for the if branch
	# generate code for the right-hand side of the assignment
	# copy the base pointer to another register
	mov	%rbp, %rax
	# subtract the offset from the copy of the base pointer
	sub	$24, %rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -32(%rbp)
	# generate code for the deref on the left side of an expression
	mov	-32(%rbp), %rax
	push	%rax
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$4, %rax
	push	%rax
	# pop the result of the right-hand side
	pop	%rax
	# pop the result of the left-hand side
	pop	%rbx
	# move the right-hand side's value into the address pointed to by the left-hand size
	mov	%rax, (%rbx)
	# generate code for the right-hand side of the assignment
	# generate code for the left operand
	# generate code for the unary operand
	mov	-32(%rbp), %rax
	push	%rax
	# pop the unary operand
	pop	%rax
	# move the contents of the address to the result register
	mov	(%rax), %rbx
	# push the expression result
	push	%rbx
	# generate code for the right operand
	# push the integer
	mov	$0, %rax
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
	mov	%rax, -16(%rbp)
	# emit a jump to the end label
	jmp .L9
	# emit the else label
.L8:
	# generate code for the else branch
	# generating code for an ifelsestmt
	# generate code for the expression
	# generate code for the left operand
	# push the integer
	mov	$1, %rax
	push	%rax
	# generate code for the right operand
	# push the integer
	mov	$0, %rax
	push	%rax
	# pop the right operand
	pop	%rbx
	# pop the left operand
	pop	%rax
	cmp	%rax, %rbx
	jle	.L10
	mov	$1, %rax
	jmp	.L11
.L10:
	mov	$0, %rax
.L11:
	push	%rax
	# push the expression result
	push	%rax
	# emit a pop of the expression value from the stack into a register
	pop	%rax
	# emit a cmp of register's value to 0, i.e., check whether it's false
	cmp $0, %rax
	# emit a je to the else label
	je .L12
	# generate code for the if branch
	# generate code for the right-hand side of the assignment
	# copy the base pointer to another register
	mov	%rbp, %rax
	# subtract the offset from the copy of the base pointer
	sub	$16, %rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -32(%rbp)
	# generate code for the deref on the left side of an expression
	mov	-32(%rbp), %rax
	push	%rax
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$2, %rax
	push	%rax
	# pop the result of the right-hand side
	pop	%rax
	# pop the result of the left-hand side
	pop	%rbx
	# move the right-hand side's value into the address pointed to by the left-hand size
	mov	%rax, (%rbx)
	# generate code for the right-hand side of the assignment
	# generate code for the left operand
	# generate code for the unary operand
	mov	-32(%rbp), %rax
	push	%rax
	# pop the unary operand
	pop	%rax
	# move the contents of the address to the result register
	mov	(%rax), %rbx
	# push the expression result
	push	%rbx
	# generate code for the right operand
	# push the integer
	mov	$0, %rax
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
	mov	%rax, -16(%rbp)
	# emit a jump to the end label
	jmp .L13
	# emit the else label
.L12:
	# generate code for the else branch
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$0, %rax
	push	%rax
	pop	%rax
	mov	%rax, -8(%rbp)
	# emit the end label
.L13:
	# emit the end label
.L9:
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$0, %rax
	push	%rax
	pop	%rax
	mov	%rax, -8(%rbp)
	# emit a jump to the head label
	jmp .L0
	# emit the end label
.L1:
	# generate code for the return expression
	# push the integer
	mov	$123, %rax
	push	%rax
	# save the return expression into %rax per the abi
	pop	%rax
	# emit main's epilogue
	pop	%rbx
	mov	%rbp, %rsp
	pop	%rbp
	ret
