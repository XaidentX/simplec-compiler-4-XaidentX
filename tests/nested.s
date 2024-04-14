.file "stdin"
.text
.globl main
.type main, @function
main:
	# stack space for argc and argv
	# emit main's prologue
	push	%rbp
	mov	%rsp, %rbp
	sub	$64, %rsp
	push	%rbx
	# move argc and argv from parameter registers to the stack
	mov	%rdi, -56(%rbp)
	mov	%rsi, -64(%rbp)
	# generate code for the body
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$10, %rax
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
	mov	$1, %rax
	push	%rax
	pop	%rax
	mov	%rax, -24(%rbp)
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$0, %rax
	push	%rax
	pop	%rax
	mov	%rax, -32(%rbp)
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$3, %rax
	push	%rax
	pop	%rax
	mov	%rax, -40(%rbp)
	# generate code for the right-hand side of the assignment
	# generate code for the left operand
	# copy the base pointer to another register
	mov	%rbp, %rax
	# subtract the offset from the copy of the base pointer
	sub	$8, %rax
	# push the expression result
	push	%rax
	# generate code for the right operand
	# push the integer
	mov	$8, %rax
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
	mov	%rax, -48(%rbp)
	# generating code for an ifelsestmt
	# generate code for the expression
	# generate code for the left operand
	# generate code for the left operand
	mov	-32(%rbp), %rax
	push	%rax
	# generate code for the right operand
	mov	-24(%rbp), %rax
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
	# push the expression result
	push	%rax
	# generate code for the right operand
	# push the integer
	mov	$0, %rax
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
	je .L2
	# generate code for the if branch
	# generating code for a whilestmt
	# emit the head label
.L3:
	# generate code for the expression
	# emit a pop of the expression value from the stack into a register
	pop	%rax
	# emit a cmp of register's value to 0, i.e., check whether it's false
	cmp $0, %rax
	# emit a je to the end label
	je .L4
	# generate code for the if branch
	# generating code for an ifelsestmt
	# generate code for the expression
	# generate code for the left operand
	# generate code for the left operand
	mov	-32(%rbp), %rax
	push	%rax
	# generate code for the right operand
	mov	-24(%rbp), %rax
	push	%rax
	# pop the right operand
	pop	%rbx
	# pop the left operand
	pop	%rax
	# conjuction &&
	cmp $0, %rax
	je .L5
	cmp $0, %rbx
	je .L5
	mov	$1, %rax
	jmp .L6
.L5:
	mov	$0, %rax
.L6:
	# push the expression result
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
	je .L7
	# generate code for the if branch
	# generate code for the deref on the left side of an expression
	mov	-48(%rbp), %rax
	push	%rax
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$25, %rax
	push	%rax
	# pop the result of the right-hand side
	pop	%rax
	# pop the result of the left-hand side
	pop	%rbx
	# move the right-hand side's value into the address pointed to by the left-hand size
	mov	%rax, (%rbx)
	# emit a jump to the end label
	jmp .L8
	# emit the else label
.L7:
	# generate code for the else branch
	# generate code for the right-hand side of the assignment
	# generate code for the left operand
	mov	-32(%rbp), %rax
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
	mov	%rax, -32(%rbp)
	# generate code for the deref on the left side of an expression
	mov	-48(%rbp), %rax
	push	%rax
	# generate code for the right-hand side of the assignment
	mov	-32(%rbp), %rax
	push	%rax
	# pop the result of the right-hand side
	pop	%rax
	# pop the result of the left-hand side
	pop	%rbx
	# move the right-hand side's value into the address pointed to by the left-hand size
	mov	%rax, (%rbx)
	# emit the end label
.L8:
	# generate code for the right-hand side of the assignment
	# generate code for the left operand
	mov	-32(%rbp), %rax
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
	mov	%rax, -32(%rbp)
	# emit a jump to the head label
	jmp .L3
	# emit the end label
.L4:
	# emit a jump to the end label
	jmp .L9
	# emit the else label
.L2:
	# generate code for the else branch
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$0, %rax
	push	%rax
	pop	%rax
	mov	%rax, -24(%rbp)
	# generate code for the deref on the left side of an expression
	mov	-48(%rbp), %rax
	push	%rax
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$0, %rax
	push	%rax
	# pop the result of the right-hand side
	pop	%rax
	# pop the result of the left-hand side
	pop	%rbx
	# move the right-hand side's value into the address pointed to by the left-hand size
	mov	%rax, (%rbx)
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$0, %rax
	push	%rax
	pop	%rax
	mov	%rax, -32(%rbp)
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$1, %rax
	push	%rax
	pop	%rax
	mov	%rax, -40(%rbp)
	# generate code for the deref on the left side of an expression
	mov	-48(%rbp), %rax
	push	%rax
	# generate code for the right-hand side of the assignment
	# push the integer
	mov	$1, %rax
	push	%rax
	# pop the result of the right-hand side
	pop	%rax
	# pop the result of the left-hand side
	pop	%rbx
	# move the right-hand side's value into the address pointed to by the left-hand size
	mov	%rax, (%rbx)
	# emit the end label
.L9:
	# generate code for the return expression
	# generate code for the unary operand
	mov	-48(%rbp), %rax
	push	%rax
	# pop the unary operand
	pop	%rax
	# move the contents of the address to the result register
	mov	(%rax), %rbx
	# push the expression result
	push	%rbx
	# save the return expression into %rax per the abi
	pop	%rax
	# emit main's epilogue
	pop	%rbx
	mov	%rbp, %rsp
	pop	%rbp
	ret
