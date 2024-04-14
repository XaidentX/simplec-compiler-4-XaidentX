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
	mov	$13, %rax
	push	%rax
	pop	%rax
	mov	%rax, -16(%rbp)
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
	je .L0
	cmp $0, %rbx
	je .L0
	mov	$1, %rax
	jmp .L1
.L0:
	mov	$0, %rax
.L1:
	push	%rax
	# push the expression result
	push	%rax
	# emit a pop of the expression value from the stack into a register
	pop	%rax
	# emit a cmp of register's value to 0, i.e., check whether it's false
	cmp $0, %rax
	# emit a je to the end label
	je .L2
	# generate code for the if branch
	# generate code for the right-hand side of the assignment
	# copy the base pointer to another register
	mov	%rbp, %rax
	# subtract the offset from the copy of the base pointer
	sub	$16, %rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -24(%rbp)
	# generate code for the deref on the left side of an expression
	mov	-24(%rbp), %rax
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
	mov	-24(%rbp), %rax
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
	# do the addition
	add	%rbx, %rax
	push	%rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -8(%rbp)
	# emit the end label
.L2:
	# generating code for an ifstmt
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
	# conjuction &&
	cmp $0, %rax
	je .L3
	cmp $0, %rbx
	je .L3
	mov	$1, %rax
	jmp .L4
.L3:
	mov	$0, %rax
.L4:
	push	%rax
	# push the expression result
	push	%rax
	# emit a pop of the expression value from the stack into a register
	pop	%rax
	# emit a cmp of register's value to 0, i.e., check whether it's false
	cmp $0, %rax
	# emit a je to the end label
	je .L5
	# generate code for the if branch
	# generate code for the right-hand side of the assignment
	# copy the base pointer to another register
	mov	%rbp, %rax
	# subtract the offset from the copy of the base pointer
	sub	$8, %rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -24(%rbp)
	# generate code for the deref on the left side of an expression
	mov	-24(%rbp), %rax
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
	mov	-24(%rbp), %rax
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
	# do the addition
	add	%rbx, %rax
	push	%rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -8(%rbp)
	# emit the end label
.L5:
	# generating code for an ifstmt
	# generate code for the expression
	# generate code for the left operand
	# push the integer
	mov	$0, %rax
	push	%rax
	# generate code for the right operand
	# push the integer
	mov	$0, %rax
	push	%rax
	# pop the right operand
	pop	%rbx
	# pop the left operand
	pop	%rax
	# conjuction &&
	cmp $0, %rax
	je .L6
	cmp $0, %rbx
	je .L6
	mov	$1, %rax
	jmp .L7
.L6:
	mov	$0, %rax
.L7:
	push	%rax
	# push the expression result
	push	%rax
	# emit a pop of the expression value from the stack into a register
	pop	%rax
	# emit a cmp of register's value to 0, i.e., check whether it's false
	cmp $0, %rax
	# emit a je to the end label
	je .L8
	# generate code for the if branch
	# generate code for the right-hand side of the assignment
	# copy the base pointer to another register
	mov	%rbp, %rax
	# subtract the offset from the copy of the base pointer
	sub	$16, %rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -24(%rbp)
	# generate code for the deref on the left side of an expression
	mov	-24(%rbp), %rax
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
	mov	-24(%rbp), %rax
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
	# do the addition
	add	%rbx, %rax
	push	%rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -8(%rbp)
	# emit the end label
.L8:
	# generating code for an ifstmt
	# generate code for the expression
	# generate code for the left operand
	# push the integer
	mov	$0, %rax
	push	%rax
	# generate code for the right operand
	# push the integer
	mov	$0, %rax
	push	%rax
	# pop the right operand
	pop	%rbx
	# pop the left operand
	pop	%rax
	# conjuction &&
	cmp $0, %rax
	je .L9
	cmp $0, %rbx
	je .L9
	mov	$1, %rax
	jmp .L10
.L9:
	mov	$0, %rax
.L10:
	push	%rax
	# push the expression result
	push	%rax
	# emit a pop of the expression value from the stack into a register
	pop	%rax
	# emit a cmp of register's value to 0, i.e., check whether it's false
	cmp $0, %rax
	# emit a je to the end label
	je .L11
	# generate code for the if branch
	# generate code for the right-hand side of the assignment
	# copy the base pointer to another register
	mov	%rbp, %rax
	# subtract the offset from the copy of the base pointer
	sub	$8, %rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -24(%rbp)
	# generate code for the deref on the left side of an expression
	mov	-24(%rbp), %rax
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
	mov	-24(%rbp), %rax
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
	# do the addition
	add	%rbx, %rax
	push	%rax
	# push the expression result
	push	%rax
	pop	%rax
	mov	%rax, -8(%rbp)
	# emit the end label
.L11:
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
	je .L12
	cmp $0, %rbx
	je .L12
	mov	$1, %rax
	jmp .L13
.L12:
	mov	$0, %rax
.L13:
	push	%rax
	# push the expression result
	push	%rax
	# emit a pop of the expression value from the stack into a register
	pop	%rax
	# emit a cmp of register's value to 0, i.e., check whether it's false
	cmp $0, %rax
	# emit a je to the end label
	je .L14
	# generate code for the if branch
	# generate code for the right-hand side of the assignment
	# generate code for the left operand
	mov	-8(%rbp), %rax
	push	%rax
	# generate code for the right operand
	# push the integer
	mov	$6, %rax
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
.L14:
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
