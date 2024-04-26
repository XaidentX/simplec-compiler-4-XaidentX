#include <stdio.h>

#include "codegen.h"
#include "table.h"

FILE *codegenout;  // the output of code generation

#define PUSH(arg1) fprintf(codegenout,  "\tpush\t%s\n", arg1 )
#define POP(arg1) fprintf(codegenout,  "\tpop\t%s\n", arg1 )
#define MOV(arg1, arg2) fprintf(codegenout, "\tmov\t%s, %s\n", arg1, arg2)
#define MOV_FROM_IMMEDIATE(arg1, arg2) fprintf(codegenout, "\tmov\t$%d, %s\n", arg1, arg2)
#define MOV_FROM_OFFSET(offset, reg) fprintf(codegenout, "\tmov\t-%d(%%rbp), %s\n", offset, reg)
#define MOV_TO_OFFSET(reg, offset) fprintf(codegenout, "\tmov\t%s, -%d(%%rbp)\n", reg, offset)
#define MOV_FROM_GLOBAL(reg, global) fprintf(codegenout, "\tmov\t%s(%%rip), %s\n", global, reg)
#define MOV_TO_GLOBAL(reg, global) fprintf(codegenout, "\tmov\t%s, %s(%%rip)\n", reg, global)
#define ADD(arg1, arg2) fprintf(codegenout, "\tadd\t%s, %s\n", arg1, arg2)
#define SUB(arg1, arg2) fprintf(codegenout, "\tsub\t%s, %s\n", arg1, arg2)
#define SUBCONST(arg1, arg2) fprintf(codegenout, "\tsub\t$%d, %s\n", arg1, arg2)
#define IMUL(arg1, arg2) fprintf(codegenout, "\timul\t%s, %s\n", arg1, arg2)
#define CDQ() fprintf(codegenout, "\tcdq\n")
#define IDIV(reg) fprintf(codegenout, "\tidiv\t%s\n", reg)
#define CALL(arg1) fprintf(codegenout, "\tcall\t%s\n", arg1)
#define RET fprintf(codegenout, "\tret\n")
#define COMMENT(arg1) fprintf(codegenout, "\t# %s\n", arg1)

#define CMP0(arg) fprintf(codegenout,"\tcmp $0, %s\n", arg)
#define CMP(arg1, arg2) fprintf(codegenout,"\tcmp %s, %s\n", arg1, arg2)
#define JE(labelnum) fprintf(codegenout,"\tje .L%d\n", labelnum)
#define JL(labelnum) fprintf(codegenout,"\tjl .L%d\n", labelnum)
#define JLE(labelnum) fprintf(codegenout,"\tjle .L%d\n", labelnum)
#define JG(labelnum) fprintf(codegenout,"\tjg .L%d\n", labelnum)
#define JGE(labelnum) fprintf(codegenout,"\tjge .L%d\n", labelnum)
#define JMP(labelnum) fprintf(codegenout,"\tjmp .L%d\n", labelnum)
#define LABEL(labelnum) fprintf(codegenout,".L%d:\n", labelnum)
#define JNE(labelnum) fprintf(codegenout,"\tjne .L%d\n", labelnum)

static int labelCount = 0;

const string const param_registers[] = { "%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"}; // all const

static void codegen_main(T_main main);

static void codegen_decllist(T_decllist decllist);

static void codegen_stmtlist(T_stmtlist stmtlist);

static void codegen_funclist(T_funclist funclist);

static void codegen_func(T_func func);

static void codegen_stmtlist(T_stmtlist stmtlist);

static void codegen_stmt(T_stmt stmt);

static void codegen_assignstmt(T_stmt stmt);

static void codegen_ifstmt(T_stmt stmt);

static void codegen_ifelsestmt(T_stmt stmt);

static void codegen_whilestmt(T_stmt stmt);

static void codegen_compoundstmt(T_stmt stmt);

static void codegen_expr(T_expr expr);

static void codegen_identexpr(T_expr expr);

static void codegen_callexpr(T_expr expr);

static void codegen_intexpr(T_expr expr);

static void codegen_charexpr(T_expr expr);

static void codegen_strexpr(T_expr expr);

static void codegen_arrayexpr(T_expr expr);

static void codegen_unaryexpr(T_expr expr);

static void codegen_binaryexpr(T_expr expr);

static void codegen_castexpr(T_expr expr);

static void emit_prologue(int size);

static void emit_epilogue();

static int bitwidth(T_type type);

typedef struct S_offset_scope *T_offset_scope;

struct S_offset_scope {
  T_table table;
  int stack_size;
  int current_offset;
  T_offset_scope parent;
};

static T_offset_scope create_offset_scope(T_offset_scope parent) {
  T_offset_scope offset_scope = xmalloc(sizeof(*offset_scope));
  offset_scope->table = create_table();
  // start after the dynamic link to the caller's %rbp
  offset_scope->current_offset = 8;
  offset_scope->stack_size = 0;
  offset_scope->parent = parent;
  return offset_scope;
}

static T_offset_scope destroy_offset_scope(T_offset_scope offset_scope) {
  T_offset_scope parent_offset_scope = offset_scope->parent;
  destroy_table(offset_scope->table);
  free(offset_scope);
  return parent_offset_scope;
}

struct S_offset {
  int offset;
};

typedef struct S_offset * T_offset;

static T_table global_symbols;

static T_offset_scope current_offset_scope;

void insert_offset(T_offset_scope scope, string ident, int size) {
  T_offset entry = xmalloc(sizeof(*entry));
  entry->offset = scope->current_offset;
  insert(scope->table, ident, (void*) entry);
  scope->stack_size += size;
  scope->current_offset += size;
}

static int lookup_offset_in_scope(T_offset_scope offset_scope, string ident) {
  T_offset offset = (T_offset) lookup(offset_scope->table, ident);
  if (NULL == offset) {
    fprintf(stderr, "FATAL: symbol not in table.  double-check the code that inserts the symbol into the offset scope.");
  }
  return offset->offset;
}

static T_offset lookup_offset_in_all_offset_scopes(T_offset_scope offset_scope, string ident) {
  // loop over each offset_scope and check for a binding for ident
  while (NULL != offset_scope) {
    // check for a binding in this offset_scope
    T_offset offset = (T_offset) lookup(offset_scope->table, ident);
    if (NULL != offset) {
      return offset;
    }
    // no binding in this offset_scope, so check the parent
    offset_scope = offset_scope->parent;
  }
  // found no binding in any offset_scope
  return NULL;
}

void codegen(T_prog prog) {
  // no need to record symbols in the global offset_scope.  the assembler and linker handle them.
  current_offset_scope = NULL;
  
  // emit assembly header
  fprintf(codegenout, ".file \"stdin\"\n");
  
  // emit a .comm for global vars
  global_symbols = create_table();
  // loop over each global symbol.  emit .comm and add to global symtab
  T_decllist decllist = prog->decllist;
  while (NULL != decllist) {
    if (E_functiontype != decllist->decl->type->kind) {
      fprintf(codegenout, ".comm\t%s,%d\n", decllist->decl->ident, bitwidth(decllist->decl->type));
      insert(global_symbols, decllist->decl->ident, decllist->decl->ident);
    }
    decllist = decllist->tail;
  }

  // optional: emit an .rodata section and label for strings

  // go through each function
  codegen_funclist(prog->funclist);

  // generate the code for main
  codegen_main(prog->main);

  // free the global symbol table
  free(global_symbols);
}

static void codegen_main(T_main main) {
  // create a new scope
  current_offset_scope = create_offset_scope(NULL);

  // emit the pseudo ops for the function definition
  fprintf(codegenout, ".text\n");
  fprintf(codegenout, ".globl %s\n", "main");
  fprintf(codegenout, ".type %s, @function\n", "main");

  // emit a label for the function
  fprintf(codegenout, "%s:\n", "main");

  // add local declarations to the scope
  codegen_decllist(main->decllist);

  COMMENT("stack space for argc and argv");
  insert_offset(current_offset_scope, "argc", 8);  // int argc
  insert_offset(current_offset_scope, "argv", 8);  // char **argv

  COMMENT("emit main's prologue");
  emit_prologue(current_offset_scope->stack_size);

  COMMENT("move argc and argv from parameter registers to the stack");
  int offset;
  offset = lookup_offset_in_scope(current_offset_scope, "argc");
  MOV_TO_OFFSET("%rdi", offset);
  offset = lookup_offset_in_scope(current_offset_scope, "argv");
  MOV_TO_OFFSET("%rsi", offset);
  
  COMMENT("generate code for the body");
  codegen_stmtlist(main->stmtlist);

  COMMENT("generate code for the return expression");
  codegen_expr(main->returnexpr);
  COMMENT("save the return expression into %rax per the abi");
  POP("%rax");

  COMMENT("emit main's epilogue");
  emit_epilogue();

  // exit the scope
  current_offset_scope = destroy_offset_scope(current_offset_scope);
}

static void codegen_funclist(T_funclist funclist) {
  while (NULL != funclist) {
    codegen_func(funclist->func);
    funclist = funclist->tail;
  }
}

static void codegen_func(T_func func) {
//  fprintf(stderr, "TODO: codegen_func (remove this message when implemented).");

  // Create a new scope for the function.
  current_offset_scope = create_offset_scope(current_offset_scope);

  // Emit the pseudo ops for the functions definition.
  fprintf(codegenout, ".text\n");
  fprintf(codegenout, ".globl %s\n", func->ident);
  fprintf(codegenout, ".type %s, @function\n", func->ident);

  // Emit a label for the function.
  fprintf(codegenout, "%s:\n", func->ident);

  // Insert the parameter into the offset table.
  insert_offset(current_offset_scope, func->paramlist->ident, 8);

  // Add local declarations to the scope.
  codegen_decllist(func->decllist);

  // Emit the function prologue.
  COMMENT("emit the function prologue");
  emit_prologue(current_offset_scope->stack_size);

  // Move the one parameter onto the stack.
  COMMENT("move parameter onto the stack");
  int offset = lookup_offset_in_scope(current_offset_scope, func->paramlist->ident);
  MOV_TO_OFFSET("%rdi", offset);

  // Generate code for the body of the function.
  COMMENT("generate code for the body");
  codegen_stmtlist(func->stmtlist);

  // Generate code for the return expression.
  COMMENT("generate code for the return expression");
  codegen_expr(func->returnexpr);

  COMMENT("save the return expression into %rax per the abi");
  POP("%rax");

  // Emit the epilogue
  COMMENT("emit the epilogue");
  emit_epilogue();

  // Destroy the function's scope
  current_offset_scope = destroy_offset_scope(current_offset_scope);
}

static void codegen_decllist(T_decllist decllist) {
//  fprintf(stderr, "TODO: codegen_decllist (remove this message when implemented).");

  // Loop over each element in the decllist list.
  while(decllist != NULL){

    // Insert each element into the offset_scope.
    insert_offset(current_offset_scope, decllist->decl->ident, 8);

    decllist = decllist->tail;

}
}

/* statements */
static void codegen_stmtlist(T_stmtlist stmtlist) {
  while (NULL != stmtlist) {
    codegen_stmt(stmtlist->stmt);
    stmtlist = stmtlist->tail;
  }
}

static void codegen_stmt(T_stmt stmt) {
  if (NULL == stmt) {
    fprintf(stderr, "FATAL: stmt is NULL in codegen_stmt\n");
    exit(1);
  }
  switch (stmt->kind) {
  case E_assignstmt: codegen_assignstmt(stmt); break;
  case E_ifstmt: codegen_ifstmt(stmt); break;
  case E_ifelsestmt: codegen_ifelsestmt(stmt); break;
  case E_whilestmt: codegen_whilestmt(stmt); break;
  case E_compoundstmt: codegen_compoundstmt(stmt); break;
  default: fprintf(stderr, "FATAL: unexpected stmt kind in codegen_stmt\n"); exit(1); break;
  }
}

static void codegen_assignstmt(T_stmt stmt) {

  if (stmt->assignstmt.left->kind == E_unaryexpr){

    COMMENT("generate code for the deref on the left side of an expression");
    codegen_expr(stmt->assignstmt.left->unaryexpr.expr);

    COMMENT("generate code for the right-hand side of the assignment");
    codegen_expr(stmt->assignstmt.right);

    COMMENT("pop the result of the right-hand side");
    POP("%rbx");

    COMMENT("pop the result of the left-hand side");
    POP("%rax");

    COMMENT("move the right-hand side's value into the address pointed to by the left-hand size using memory indirect addressing");
    MOV("%rbx", "(%rax)");

  } else {

    COMMENT("generate code for the right-hand side of the assignment");
    codegen_expr(stmt->assignstmt.right);

    COMMENT("pop the result of the right-hand side");
    POP("%rax");

    COMMENT("Lookup the identifier to find its offset");
    int offset = lookup_offset_in_scope(current_offset_scope, stmt->assignstmt.left->identexpr);

    COMMENT("Move the register that holds the right hand side of the expression into the stack address");
    MOV_TO_OFFSET("%rax", offset);

  }
}

/*
  // Generate code for the right hand side of the assignment.
  COMMENT("generate code for the right-hand side of the assignment");
  codegen_expr(stmt->assignstmt.right);

  // Pop it from the stack.
   POP("%rax");

  // Find the address of the left hand side of the assignment.
  T_expr left_expr = stmt->assignstmt.left;

  if (left_expr->kind == E_identexpr){

   // POP("%rax");

    // Lookup the identifier to find its offset.
    int offset = lookup_offset_in_scope(current_offset_scope, left_expr->identexpr);

    // Move the register that holds the right hand side of the expression into the stack address.
    MOV_TO_OFFSET("%rax", offset);

  } else if (left_expr->kind == E_unaryexpr){
       
    // Generate code for the expression inside the dereference operator
    codegen_expr(left_expr->unaryexpr.expr);

    // Pop the result (address) from the stack into a register
    //POP("%rbx");
    POP("%rax");

    // Move the value to be assigned into the memory location pointed by the address
    //MOV("%rax", "(%rbx)");
    MOV("%rbx", "(%rax)");

    
  }

*/

static void codegen_ifstmt(T_stmt stmt) {

  // evaluate the condition expression
  codegen_expr(stmt->ifstmt.cond);

  // store result in %rax
  POP("%rax");

  // compare the result to false
  CMP0("%rax");

  // Label for the jump
  int falseLabel = labelCount++;

  // Jump only if the condition is false.
  JE(falseLabel);

  // Generate code for the contents of the if branch.
  codegen_stmt(stmt->ifstmt.body);

  // Label for the end of the if statement
  LABEL(falseLabel);
  
}

static void codegen_ifelsestmt(T_stmt stmt) {

  // evaluate the condition expression.
  codegen_expr(stmt->ifelsestmt.cond);

  // store result in %rax
  POP("%rax");

  // compare to "false"
  CMP0("%rax");

  // label for the else branch
  int elseLabel = labelCount++;

  // jump only if false to the else branch
  JE(elseLabel);

  // contents of the if branch
  codegen_stmt(stmt->ifelsestmt.ifbranch);

  // unconditionally jump past else branch
  int endLabel = labelCount++;
  JMP(endLabel);

  // Contents of the else branch
  LABEL(elseLabel);
  codegen_stmt(stmt->ifelsestmt.elsebranch);

  // Label for the end of the if-else statement
  LABEL(endLabel);
  

}

static void codegen_whilestmt(T_stmt stmt) {
  
    int loopLabel = labelCount++;
    int exitLabel = labelCount++;
    
    // Label for the head of the loop
    LABEL(loopLabel);

    // evaluate the condition expression
    codegen_expr(stmt->whilestmt.cond);

    // store result in %rax
    POP("%rax");

    // compare to "false"
    CMP0("%rax");

    // jump only if false
    JE(exitLabel);

    // contents of the while body
    codegen_stmt(stmt->whilestmt.body);

    // unconditionally jump to loop head
    JMP(loopLabel);

    LABEL(exitLabel);

}

static void codegen_compoundstmt(T_stmt stmt) {

  // Generate the code for the body of the compound statement.
  codegen_stmtlist(stmt->compoundstmt.stmtlist);

}

/* expressions */
static void codegen_expr(T_expr expr) {
  if (NULL == expr) {
    fprintf(stderr, "FATAL: unexpected NULL in codegen_expr\n");
    exit(1);
  }
  switch (expr->kind) {
  case E_identexpr: codegen_identexpr(expr); break;
  case E_callexpr: codegen_callexpr(expr); break;
  case E_intexpr: codegen_intexpr(expr); break;
  case E_charexpr: codegen_charexpr(expr); break;
  case E_strexpr: codegen_strexpr(expr); break;
  case E_arrayexpr: codegen_arrayexpr(expr); break;
  case E_unaryexpr: codegen_unaryexpr(expr); break;
  case E_binaryexpr: codegen_binaryexpr(expr); break;
  case E_castexpr: codegen_castexpr(expr); break;
  default: fprintf(stderr, "FATAL: unexpected expr kind in codegen_expr\n"); exit(1); break;
  }
}

static void codegen_identexpr(T_expr expr) {
  // todo: given in class
  //look up the ident, then move it to an intermidate register
  int offset = lookup_offset_in_scope(current_offset_scope, expr->identexpr);
  MOV_FROM_OFFSET(offset, "%rax");
  PUSH("%rax");
}

static void codegen_callexpr(T_expr expr) {

  // Generate code for the parameter's expression.
  codegen_expr(expr->callexpr.args->expr);

  // Pass the parameter to the callee via the %rdi register.
  POP("%rdi");

  // Emit the call instruction to the function's identifier.
  CALL(expr->callexpr.ident);

  // Save the return value by pushing it onto the stack.
  PUSH("%rax");
}

static void codegen_intexpr(T_expr expr) {

  // Move the immediate value into a register and push it onto the stack.
  MOV_FROM_IMMEDIATE((int)expr->intexpr, "%rax");

  PUSH("%rax");
}

static void codegen_charexpr(T_expr expr) {
  COMMENT("push the character");
  MOV_FROM_IMMEDIATE((int) expr->charexpr, "%rax");
  PUSH("%rax");
}

static void codegen_strexpr(T_expr expr) {
  // bonus exercise
}

static void codegen_arrayexpr(T_expr expr) {
  // bonus exercise
}

static void codegen_unaryexpr(T_expr expr) {

  // Error handling
  if (expr == NULL || expr->unaryexpr.expr == NULL) {
    // Handle the error appropriately, perhaps by printing an error message or returning early
    fprintf(stderr, "Error: NULL pointer encountered in codegen_unaryexpr\n");
    return;
  }
  

  switch(expr->unaryexpr.op){

    case E_op_ref:

     if (expr->unaryexpr.expr->kind == E_identexpr){

      MOV("%rbp", "%rax"); // Save the base pointer to %rax

      int offset = lookup_offset_in_scope(current_offset_scope, expr->unaryexpr.expr->identexpr);

      SUBCONST(offset, "%rax"); // Subtract the offset from the base pointer

      PUSH("%rax"); // Push the address onto the stack

     }else {
        fprintf(stderr, "Error: E_op_red: Cannot reference a non-identifier expression\n");  
    }

    break;

    case E_op_deref:
    
    // Generate code for the expression inside the dereference expression
    codegen_expr(expr->unaryexpr.expr);

    // Retrieve the value from the stack by popping it
    POP("%rbx");

    // Use memory indirection addressing to move the contents of the memory address to a register
    MOV("(%rbx)", "%rax");

    // Save the result onto the stack
    PUSH("%rax");
    
    break;

    
    case E_op_not:
    
    // Generate code for the expression inside the not operator
    codegen_expr(expr->unaryexpr.expr);

    // Retrieve the value from the stack by popping it
    POP("%rax");

    // Compare with 0
    CMP0("%rax");

    // jump if false
    int falseLabel = labelCount++;
    JE(falseLabel);

    // Move 0 to rax
    MOV_FROM_IMMEDIATE(0, "%rax");

    // Jump to the label after the one used for JE
    int endLabel = labelCount++;
    JMP(endLabel);
    
    // Label for JE
    LABEL(falseLabel);

    // Move 1 to rax
    MOV_FROM_IMMEDIATE(1, "%rax");  

    // Label for JMP
    LABEL(endLabel);
   
    PUSH("%rax");
    
    break;
  }
  


}

static void codegen_binaryexpr(T_expr expr) {
//  fprintf(stderr, "TODO: codegen_binaryexpr (remove this message when implemented).");

    // Generate code for the left and right operands of the current expression.
  COMMENT("generate code for the left operand");
  codegen_expr(expr->binaryexpr.left);
  COMMENT("generate code for the right operand");
  codegen_expr(expr->binaryexpr.right);

  // Pop the result of each operand (the right one will be first, since it was pushed last).
  COMMENT("pop the right operand");
  POP("%rbx");
  COMMENT("pop the left operand");
  POP("%rax");

  // Compute the result of the current expression.
  switch(expr->binaryexpr.op){

    case E_op_plus:
      COMMENT("do the addition");
      ADD("%rbx", "%rax");
      break;

    case E_op_minus:
      COMMENT("do the subtraction");
      SUB("%rbx", "%rax");
      break;

    case E_op_times:
      COMMENT("do the multiplication");
      IMUL("%rbx", "%rax");
      break;

    case E_op_divide:
      COMMENT("do the division");
      CDQ();
      IDIV("%rbx");
      // quotient is in %rax
      break;

    case E_op_mod:
      COMMENT("do the remainder");
      CDQ();
      IDIV("%rbx");
      // remainder is in %rdx
      MOV("%rdx", "%rax");
      break;

    
    case E_op_and:

      // Test the left operand
      CMP0("%rax");

      // Jump only if false
      JE(labelCount);

      // Test right operand
      CMP0("%rbx");

      // Jump only if false
      int falseLabel = labelCount++;
      JE(falseLabel);

      // Set result (%rax) to true
      MOV_FROM_IMMEDIATE(1, "%rax");

      // Jump to end label
      int endLabel = labelCount++;
      JMP(endLabel);

      // Label for false result
      LABEL(falseLabel);

      // Set result (%rax) to false
      MOV_FROM_IMMEDIATE(0, "%rax");

      // Label for end of expression
      LABEL(endLabel);

      break;
      
    case E_op_or:

      // Test the left operand
      CMP0("%rax");

      // jump only if NOT false
      int trueLabel = labelCount++;
      JNE(trueLabel);

      // test right operand
      CMP0("%rbx");

      // jump only if NOT false
      JNE(trueLabel);

      // set result (%rax) to false
      MOV_FROM_IMMEDIATE(0, "%rax");

      // jump
      endLabel = labelCount++;
      JMP(endLabel);

      // true label
      LABEL(trueLabel);

      // set result (%rax) to true
      MOV_FROM_IMMEDIATE(1, "%rax");

      // first instruction after the "or" operation
      LABEL(endLabel);

      break;

    case E_op_eq:

      // Compare the two operands
      CMP("%rax", "%rbx"); 
      
      // Jump to labelCount if operands are equal
      trueLabel = labelCount++;
      JE(trueLabel);

      // Move 0 to %rax (not equal case)
      MOV_FROM_IMMEDIATE(0, "%rax");

      // Jump to end label
      endLabel = labelCount++;
      JMP(endLabel);

      // Label for equal case
      LABEL(trueLabel);

      // Move 1 to %rax (equal case)
      MOV_FROM_IMMEDIATE(1, "%rax");

      // End label
      LABEL(endLabel);

      break;

    case E_op_lt:
    
      // Compare the two operands
      CMP("%rbx", "%rax");

      // Jump if the left operand is greater than the right operand
      int greaterThan = labelCount++;
      JGE(greaterThan);   

      // Set result to 1 (true) for left less than right
      MOV_FROM_IMMEDIATE(1, "%rax");  

      // Unconditionally jump to skip setting the result to 0 (false)
      endLabel = labelCount++;
      JMP(endLabel);

      // Label for when the left operand is greater than the right operand
      LABEL(greaterThan);

      // Set result to 0 (false) for left greater than right
      MOV_FROM_IMMEDIATE(0, "%rax");  

      // End label
      LABEL(endLabel);
      
      break;
      

    default:
      fprintf(stderr, "ERROR: Unsupported binary operation.\n");
      exit(1);

   
  }

  // Push the result onto the stack.
  COMMENT("push the expression result");
  PUSH("%rax");
}

static void codegen_castexpr(T_expr expr) {
  // bonus: truncate or extend data between bitwidths depending on type  
  codegen_expr(expr->castexpr.expr);
}

/**
 * Emit a function prologue, given some size in bytes of the local
 * variables in the stack frame.
 */
static void emit_prologue(int size) {
	//save stack
	PUSH("%rbp");
	MOV("%rsp", "%rbp");
	if (size > 0) {
		SUBCONST(size, "%rsp");
	}
	PUSH("%rbx");
}

static void emit_epilogue() {
	POP("%rbx");
	MOV("%rbp", "%rsp");
	POP("%rbp");
	RET;
}

/**
 * This function returns the size of a type in bytes.
 */
static int bitwidth(T_type type) {
  switch (type->kind) {
  case E_primitivetype:
    switch (type->primitivetype) {
    case E_typename_int:
      // 32-bit integers
      return 4;
    case E_typename_char:
      // characters are 1 byte
      return 1;
    default:
      fprintf(stderr, "FATAL: unexpected kind in compare_types\n");
      exit(1);
    }
    break;
  case E_pointertype:
    // pointers are to 64-bit addresses
    return 8;
  case E_arraytype:
    // arrays are the size times the bitwidth of the type
    return type->arraytype.size * bitwidth(type->arraytype.type);
  case E_functiontype:
    fprintf(stderr, "FATAL: functions as values are not supported\n");
    exit(1);
    break;
  default:
    fprintf(stderr, "FATAL: unexpected kind in bitwidth\n");
    exit(1);
    break;
  }  
}
