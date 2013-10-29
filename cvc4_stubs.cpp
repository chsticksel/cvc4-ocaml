/* OCaml bindings for CVC4
  
   Copyright 2013 Christoph Sticksel

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
   
   http://www.apache.org/licenses/LICENSE-2.0
   
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
   
*/

/* These are the stubs for the functions exported to OCaml. 
   
   We have three types: cvc4_solver, cvc4_type and cvc4_expr. The last
   two types manage their memory and delete the allocated memory when
   the values become garbage collected. A value of cvc4_solver will
   leave the allocated memory behind when it is garbage collected,
   there is currently no function to delete its memory.
   
   TODO: How to hash a type? There is no getId method as for expressions.
   
*/

extern "C" {

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

}

#include <cvc4/cvc4.h>

// #define DEBUG

/* Positions of pointers in cvc4_solver abstract datatype fields */
#define em_field 0
#define smt_field 1
#define stack_level_field 2
#define symtab_field 3 

/* Define lifted booleans as OCaml integers */
#define Val_l_True Val_int(0)
#define Val_l_False Val_int(1)
#define Val_l_Undef Val_int(2)

/* Values for type cvc4_sat_result */
#define Val_UNSAT Val_int(0)
#define Val_SAT Val_int(1)
#define Val_SAT_UNKNOWN Val_int(2)

/* Values for type cvc4_validity_result */
#define Val_INVALID Val_int(0)
#define Val_VALID Val_int(1)
#define Val_VALIDITY_UNKNOWN Val_int(2)


using namespace CVC4;


/* Macro to get the expression stored in the data field of a custom block */
#define cvc4_expr_val(v) (*(Expr**) Data_custom_val(v))


/* Macro to get the type stored in the data field of a custom block */
#define cvc4_type_val(v) (*(Type**) Data_custom_val(v))


/* Finalize an expression when it is garbage collected by OCaml */
void custom_finalize_cvc4_expr(value expr_in) {

  /* Get the pointer to the expression from the data part of our custom block */
  Expr* expr = cvc4_expr_val(expr_in);


#ifdef DEBUG
  std::cerr << "Deleting " << *expr << std::endl;
#endif

  /* Delete the expression */
  delete expr;

}


/* Finalize a type when it is garbage collected by OCaml */
void custom_finalize_cvc4_type(value type_in) {

  /* Get the pointer to the type from the data part of our custom block */
  Type* type = cvc4_type_val(type_in);

#ifdef DEBUG
  std::cerr << "Deleting " << *type << std::endl;
#endif

  /* Delete the type */
  delete type;

}


/* Comparison function for expression in custom block */
int custom_compare_cvc4_expr(value expr1_in, value expr2_in) {

  /* Get first expresssion */
  Expr* expr1 = cvc4_expr_val(expr1_in);

  /* Get second expresssion */
  Expr* expr2 = cvc4_expr_val(expr2_in);

  try {
    
    /* First expression is greater? */
    if (*expr1 > *expr2) {
      
      /* Return 1 */
      return 1;
      
      /* Second expression is greater? */
    } else if (*expr1 < *expr2) {
      
      /* Return -1 */
      return -1;
      
      /* Expressions are equal */
    } else {
      
      /* Return 0 */
      return 0;
      
    }
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Comparison function for type in custom block */
int custom_compare_cvc4_type(value type1_in, value type2_in) {

  /* Get first type */
  Type* type1 = cvc4_type_val(type1_in);

  /* Get second type */
  Type* type2 = cvc4_type_val(type2_in);

  try {
    
    /* First type is greater? */
    if (*type1 > *type2) {
      
      /* Return 1 */
      return 1;
      
      /* Second type is greater? */
    } else if (*type1 < *type2) {
      
      /* Return -1 */
      return -1;
      
      /* Types are equal */
    } else {
      
      /* Return 0 */
      return 0;
      
    }
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Hash function for expression in custom block */
long custom_hash_cvc4_expr(value expr_in) {

  /* Get expresssion */
  Expr* expr = cvc4_expr_val(expr_in);

  try {

    /* Get ID of expression */
    long res = expr->getId();

    /* Return ID as hash */
    return(res);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Custom block with finalization, comparison and hash function for expression */
static struct custom_operations expr_ops = {
    identifier:     "CVC4::Expr",
    finalize:       custom_finalize_cvc4_expr,
    compare:        custom_compare_cvc4_expr,
    hash:           custom_hash_cvc4_expr,
    serialize:      custom_serialize_default,
    deserialize:    custom_deserialize_default
};


/* Custom block with finalization, comparison and hash function for type */
static struct custom_operations type_ops = {
    identifier:     "CVC4::Type",
    finalize:       custom_finalize_cvc4_type,
    compare:        custom_compare_cvc4_type,
    hash:           custom_hash_default,    /* TODO: How to hash a type? */
    serialize:      custom_serialize_default,
    deserialize:    custom_deserialize_default
};


/* Copy a CVC4 expression into an OCaml value stored as a custom block */
value copy_cvc4_expr(Expr& expr) {

  /* Allocate for expression 
     
     We should not use CAMLlocal here, this is only valid outside of
     nested blocks. Therefore we put the CAMLlocal macro at the
     beginning of the calling function and pass it as a parameter. */
  value expr_val = caml_alloc_custom(&expr_ops, sizeof(Expr*), 0, 1);
  
  /* Get a copy of the expression that we can delete when we want to */
  Expr* my_expr = new Expr(expr);
  
  /* Set pointer to our expression into the data field of our custom block */
  cvc4_expr_val(expr_val) = my_expr;

  /* Return expression */
  return expr_val;

}


/* Copy a CVC4 type into an OCaml value stored as a custom block */
value copy_cvc4_type(Type& type) {

  /* Allocate for type
     
     We should not use CAMLlocal here, this is only valid outside of
     nested blocks. Therefore we put the CAMLlocal macro at the
     beginning of the calling function and pass it as a parameter. */
  value type_val = caml_alloc_custom(&type_ops, sizeof(Type*), 0, 1);
  
  /* Get a copy of the type that we can delete when we want to */
  Type* my_type = new Type(type);
  
  /* Set pointer to our type into the data field of our custom block */
  cvc4_type_val(type_val) = my_type;

  /* Return expression */
  return type_val;

}


/* Create and return a CVC4 solver instance 

   external cvc4_create_smt_engine : bool -> cvc4_solver = "cvc4_create_smt_engine" 

   The solver is created in the C++ heap, OCaml gets only a pointer in
   an Abstract_tag. No finalization is done when the OCaml value
   becomes garbage collected.

   Every solver instance has its own expression manager that is
   created here. Since the expression manager contains the options, we
   do not share it between different instances.

*/
extern "C" CAMLprim value cvc4_create_smt_engine(value models_in, value rlimit_in)
{

#ifdef DEBUG
  std::cerr << "cvc4_create_smt_engine" << std::endl;
#endif
  
  /* Declare OCaml values */
  CAMLparam1 (models_in);
  CAMLlocal1 (res);

 /* Create new expression manager */
  ExprManager* em = new ExprManager();

  /* Create new CVC4 instance */
  SmtEngine* smt = new SmtEngine(em);

  /* Create a symbol table */
  SymbolTable* symtab = new SymbolTable();
  
  try {

    /* Enable incremental solving */
    smt->setOption("incremental", SExpr("true")); 

    /* Enable or disable models */
    if (Bool_val(models_in)) { 
      smt->setOption("produce-models", SExpr("true"));
    } else {
      smt->setOption("produce-models", SExpr("false"));
    }

    /* Set rlimit if greater than zero */
    if (Int_val(rlimit_in) > 0) {
      smt->setResourceLimit(Int_val(rlimit_in));
    }

    /* Output in SMTLIB2 format */
    // em->setOutputLanguage(language::output::LANG_SMTLIB_V2);

    /* Set logic */
    smt->setLogic("QF_UF");
  
    /* Allocate abstract datatype with four fields for CVC4 instance */
    res = caml_alloc(4, Abstract_tag);
    
    /* First field is pointer to expression manager */
    Store_field(res, em_field, (value) em); 
    
    /* Second field is pointer to SMT engine */
    Store_field(res, smt_field, (value) smt); 
    
    /* Third field is the number of context pushes */
    Store_field(res, stack_level_field, (value) 0); 

    /* Fourth field is the symbol table */
    Store_field(res, symtab_field, (value) symtab); 
    
    /* Return CVC4 instance */
    CAMLreturn(res);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }
  
}


/* Return the type of integers 

   external cvc4_get_integer_type : cvc4_solver -> cvc4_type = "cvc4_get_integer_type" 

 */
extern "C" CAMLprim value cvc4_get_integer_type(value solver_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_get_integer_type" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam1 (solver_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  try {

    /* Get integer type from expression manager */
    Type type = em->integerType();

    /* Copy type into an OCaml value */
    res = copy_cvc4_type(type);
          
    /* Return type */
    CAMLreturn(res);

  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}

/* Return the type of booleans

   external cvc4_get_bool_type : cvc4_solver -> cvc4_type = "cvc4_get_bool_type" 

 */
extern "C" CAMLprim value cvc4_get_bool_type(value solver_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_get_bool_type" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam1 (solver_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  try {

    /* Get Boolean type from expression manager */
    Type type = em->booleanType();

    /* Copy type into an OCaml value */
    res = copy_cvc4_type(type);
    
    /* Return type */
    CAMLreturn(res);

  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Create a free type of the given name 

   external cvc4_mk_type : cvc4_solver -> string -> cvc4_type = "cvc4_mk_type" 

 */
extern "C" CAMLprim value cvc4_mk_type(value solver_in, value type_name_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_mk_type" << std::endl;
#endif

  /* Declare parameters */
  CAMLparam2 (solver_in, type_name_in);

  /* Allocate for a custom datatype for type */
  CAMLlocal1 (res);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get symbol table */
  SymbolTable* symtab = (SymbolTable*) Field(solver_in, symtab_field);

  /* Get string from value */
  std::string name = std::string(String_val(type_name_in));
  
  try {

    /* Name is bound to a type in current scope? */
    if (symtab->isBoundType(name)) {
	
      /* Get type bound to name */
      Type type = symtab->lookupType(name);

      /* Copy type into an OCaml value */
      res = copy_cvc4_type(type);
          
    } else {
      
      /* Create a new variable */
      Type type = em->mkSort(name);
      
      /* Copy type into an OCaml value */
      res = copy_cvc4_type(type);
          
      /* Add binding of name to variable to symbol table */
      symtab->bindType(name, *cvc4_type_val(res), true);
      
    }
    
    /* Return type */
    CAMLreturn(res);

  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Return the propositional constant true

   external cvc4_get_true_expr : cvc4_solver -> cvc4_expr = "cvc4_get_true_expr" 

 */
extern "C" CAMLprim value cvc4_get_true_expr(value solver_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_get_true_expr" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam1 (solver_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  try {

    /* Get true constant of expression manager */
    Expr expr = em->mkConst(true);

    /* Copy expression into an OCaml value */
    res = copy_cvc4_expr(expr);
    
    /* Return type */
    CAMLreturn(res);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}

/* Return the propositional constant false

   external cvc4_get_false_expr : cvc4_solver -> cvc4_expr = "cvc4_get_false_expr" 

*/
extern "C" CAMLprim value cvc4_get_false_expr(value solver_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_get_false_expr" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam1 (solver_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  try {

     /* Get false constant of expression manager */
    Expr expr = em->mkConst(false);

    /* Copy expression into an OCaml value */
    res = copy_cvc4_expr(expr);
    
    /* Return type */
    CAMLreturn(res);

  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Create a variable of the given name and type 

   external cvc4_mk_var : cvc4_solver -> string -> cvc4_type -> cvc4_expr = "cvc4_mk_var" 

 */
extern "C" CAMLprim value cvc4_mk_var(value solver_in, value var_name_in, value type_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_mk_var" << std::endl;
#endif

  /* Declare parameters */
  CAMLparam3 (solver_in, var_name_in, type_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get symbol table */
  SymbolTable* symtab = (SymbolTable*) Field(solver_in, symtab_field);

  /* Get CVC4 type from value */
  Type* t = cvc4_type_val(type_in);

  /* Get string from value */
  std::string name = std::string(String_val(var_name_in));
  
  try {

    /* Name is bound to an expression in current scope? */
    if (symtab->isBound(name)) {
	
      /* Get expression bound to name */
      Expr expr = symtab->lookup(name);

      /* Check to make sure it is a variable */
      if (!expr.isVariable()) caml_failwith("cvc4_mk_var: name is not a variable");

      /* Copy expression bound to name into an OCaml value */
      res = copy_cvc4_expr(expr);
      
    } else {
      
      /* Create a new variable */
      Expr expr = em->mkVar(name, *t);
      
      /* Copy expression into an OCaml value */
      res = copy_cvc4_expr(expr);

      /* Add binding of name to variable to symbol table */
      symtab->bind(name, *cvc4_expr_val(res), true);
      
    }
    
    /* Return type */
    CAMLreturn(res);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }
  
}


/* Negate an expression

   external cvc4_mk_not : cvc4_solver -> cvc4_expr -> cvc4_expr = "cvc4_mk_not" 

 */
extern "C" CAMLprim value cvc4_mk_not(value solver_in, value expr_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_mk_not" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam2 (solver_in, expr_in);

  /* Allocate for a custom datatype for expression */
  CAMLlocal1 (res);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get CVC4 expression from value */
  Expr* e = cvc4_expr_val(expr_in);

  try {

    /* Get expression from expression manager */
    Expr expr = em->mkExpr(kind::NOT, *e);

    /* Copy expression into an OCaml value */
    res = copy_cvc4_expr(expr);
    
    /* Return type */
    CAMLreturn(res);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Negate an expression avoiding double negation

   external cvc4_negate : cvc4_solver -> cvc4_expr -> cvc4_expr = "cvc4_negate" 

 */
extern "C" CAMLprim value cvc4_negate(value solver_in, value expr_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_negate" << std::endl;
#endif
  
  // Declare parameters 
  CAMLparam2 (solver_in, expr_in);

  // Allocate for a custom datatype for expression
  CAMLlocal1 (res);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get CVC4 expression from value */
  Expr* e = cvc4_expr_val(expr_in);

  try {

    /* Expression is a NOT? */
    if (e->getKind() == kind::NOT) {
      
      /* Get expression under negation */
      Expr expr = e->operator[](0);
      
      /* Copy expression into an OCaml value */
      res = copy_cvc4_expr(expr);
    
    } else {
      
      /* Negate positive expression */
      Expr expr = em->mkExpr(kind::NOT, *e);

      /* Copy expression into an OCaml value */
      res = copy_cvc4_expr(expr);
    
    }
    
    /* Return type */
    CAMLreturn(res);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}

/* Create a function type of domain and range 

   The list domain_in must contain at least one element

   external cvc4_mk_function_type : cvc4_solver -> cvc4_type list -> cvc4_type -> cvc4_fun_type = "cvc4_mk_function_type" 

 */
extern "C" CAMLprim value cvc4_mk_function_type(value solver_in, value symbol_in, value domain_in, value range_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_mk_function_type" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam4 (solver_in, symbol_in, domain_in, range_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Allocate for local variables */
  CAMLlocal2 (head, type_in);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get symbol table */
  SymbolTable* symtab = (SymbolTable*) Field(solver_in, symtab_field);

  /* String of OCaml value */
  std::string symbol = std::string(String_val(symbol_in));
  
  try {

    /* Name is bound to a type in current scope? */
    if (symtab->isBound(symbol)) {
      
      /* Get type of function */
      Expr funOp = symtab->lookup(symbol);
      
#ifdef DEBUG
      std::cerr << "cvc4_mk_function_type: found " << funOp << std::endl;
#endif
  
      /* Copy expression into an OCaml value */
      res = copy_cvc4_expr(funOp);
      
      /* Return type */
      CAMLreturn(res);

    } else {

      /* Empty vector for list of domain types */
      std::vector<Type> domain;
      
      /* A type in the domain */
      Type* type;

      /* Set to head of list */
      head = domain_in;

      /* Iterate list of types */
      while (head != Val_emptylist) 
	{
	  
	  /* Get element at head of list */
	  type_in = Field(head, 0);
	  type = cvc4_type_val(type_in);
	  
	  /* Push type at head of list to end of vector */
	  domain.push_back(Type(*type));
	  
	  /* Continue with tail of list */
	  head = Field(head, 1);
	  
	}
      
      /* Get CVC4 expression from value */
      Type* range = cvc4_type_val(range_in);
      
      /* Create type of function */
      Type funType = Type(em->mkFunctionType(domain, *range));
      
      /* Create an operator expression of type */
      Expr funOp = em->mkVar(symbol, funType);

#ifdef DEBUG
      std::cerr << "cvc4_mk_function_type: created " << funOp << std::endl;
#endif
  
      /* Copy expression into an OCaml value */
      res = copy_cvc4_expr(funOp);
    
      /* Add binding of name to variable to symbol table */
      symtab->bind(symbol, *cvc4_expr_val(res), true);
      
      /* Return type */
      CAMLreturn(res);

    }

  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }
  
}


/* Create a functional expression 

   external cvc4_mk_function_expr : cvc4_solver -> cvc4_type -> cvc4_expr list -> cvc4_type -> cvc4_type = "cvc4_mk_function_expr" 

 */
extern "C" CAMLprim value cvc4_mk_function_expr(value solver_in, value op_in, value args_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_mk_function_expr" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam3 (solver_in, op_in, args_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Allocate for local variables */
  CAMLlocal2 (head, arg_in);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get operator */
  Expr* op = cvc4_expr_val(op_in);

  /* Empty vector for list of arguments */
  std::vector<Expr> opargs;
  
  /* Begin list of arguments with operator */
  opargs.push_back(*op);

  /* An argument of the function */
  Expr* arg;

  /* Set to head of list */
  head = args_in;

  /* Iterate list of arguments */
  while (head != Val_emptylist) 
    {

      /* Get element at head of list */
      arg_in = Field(head, 0);
      arg = cvc4_expr_val(arg_in);

      /* Push argument at head of list to end of vector */
      opargs.push_back(Expr(*arg));

      /* Continue with tail of list */
      head = Field(head, 1);
      
    }
  
  try {
    
    /*  Create uninterpreted function application */
    Expr expr = em->mkExpr(kind::APPLY_UF, opargs);
    
    /* Copy expression into an OCaml value */
    res = copy_cvc4_expr(expr);
    
    /* Return type */
    CAMLreturn(res);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }
  
}


/* Create a predicate type of domain 

   The list domain_in must contain at least one element

   external cvc4_mk_predicate_type : cvc4_solver -> cvc4_type list -> cvc4_pred_type = "cvc4_mk_predicate_type" 

 */
extern "C" CAMLprim value cvc4_mk_predicate_type(value solver_in, value symbol_in, value domain_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_mk_predicate_type" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam3 (solver_in, symbol_in, domain_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Allocate for local variables */
  CAMLlocal2 (head, type_in);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get symbol table */
  SymbolTable* symtab = (SymbolTable*) Field(solver_in, symtab_field);

  /* String of OCaml value */
  std::string symbol = std::string(String_val(symbol_in));
  
  try {

    /* Name is bound to a type in current scope? */
    if (symtab->isBound(symbol)) {
      
      /* Get type of function */
      Expr predOp = symtab->lookup(symbol);
      
#ifdef DEBUG
      std::cerr << "cvc4_mk_predicate_type: found " << predOp << std::endl;
#endif
  
      /* Copy expression into an OCaml value */
      res = copy_cvc4_expr(predOp);

      /* Return type */
      CAMLreturn(res);

    } else {

      /* Empty vector for list of domain types */
      std::vector<Type> domain;
  
      /* A type in the domain */
      Type* type;
      
      /* Set to head of list */
      head = domain_in;
      
      /* Iterate list of types */
      while (head != Val_emptylist) 
	{
	  
	  /* Get element at head of list */
	  type_in = Field(head, 0);
	  type = cvc4_type_val(type_in);
	  
	  /* Push type at head of list to end of vector */
	  domain.push_back(Type(*type));
	  
	  /* Continue with tail of list */
	  head = Field(head, 1);
	  
	}
      
      /* Create type of predicate */
      Type predType = Type(em->mkPredicateType(domain));
      
      /* Create an operator expression of type */
      Expr predOp = em->mkVar(symbol, predType);

#ifdef DEBUG
      std::cerr << "cvc4_mk_predicate_type: created " << predOp << std::endl;
#endif
  
      /* Copy expression into an OCaml value */
      res = copy_cvc4_expr(predOp);
    
      /* Add binding of name to variable to symbol table */
      symtab->bind(symbol, *cvc4_expr_val(res), true);
      
      /* Return type */
      CAMLreturn(res);
      
    }

  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }
  
}


/* Create a predicate expression 

   external cvc4_mk_predicate_expr : cvc4_solver -> cvc4_pred_type -> cvc4_expr list -> cvc4_expr = "cvc4_mk_predicate_expr" 

 */
extern "C" CAMLprim value cvc4_mk_predicate_expr(value solver_in, value op_in, value args_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_mk_predicate_expr" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam3 (solver_in, op_in, args_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Allocate for local variables */
  CAMLlocal2 (head, arg_in);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get operator */
  Expr* op = cvc4_expr_val(op_in);

  /* Empty vector for list of arguments */
  std::vector<Expr> opargs;
  
  /* Begin list of arguments with operator */
  opargs.push_back(*op);

  /* An argument of the function */
  Expr* arg;

  /* Set to head of list */
  head = args_in;

  /* Iterate list of arguments */
  while (head != Val_emptylist) 
    {

      /* Get element at head of list */
      arg_in = Field(head, 0);
      arg = cvc4_expr_val(arg_in);

      /* Push argument at head of list to end of vector */
      opargs.push_back(Expr(*arg));

      /* Continue with tail of list */
      head = Field(head, 1);
      
    }

  try {

    /*  Create uninterpreted function application */
    Expr expr = em->mkExpr(kind::APPLY_UF, opargs);
    
    /* Copy expression into an OCaml value */
    res = copy_cvc4_expr(expr);
    
    /* Return type */
    CAMLreturn(res);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Create an equation

   external cvc4_mk_equation : cvc4_solver -> cvc4_expr -> cvc4_expr -> cvc4_expr = "cvc4_mk_equation" 

 */
extern "C" CAMLprim value cvc4_mk_equation(value solver_in, value lhs_in, value rhs_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_mk_equation" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam3 (solver_in, lhs_in, rhs_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Get CVC4 expression from value */
  Expr* l = cvc4_expr_val(lhs_in);

  /* Get CVC4 expression from value */
  Expr* r = cvc4_expr_val(rhs_in);

  /* Get expresssion mananger and SMT engine */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  try {

    /* Create an equation */
    Expr expr = em->mkExpr(kind::EQUAL, *l, *r);
    
    /* Copy expression into an OCaml value */
    res = copy_cvc4_expr(expr);
    
    /* Return type */
    CAMLreturn(res);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Create a disjunction of expressions

   external cvc4_mk_disj : cvc4_solver -> cvc4_expr list -> cvc4_expr = "cvc4_mk_disj" 

 */
extern "C" CAMLprim value cvc4_mk_disj(value solver_in, value expr_list_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_mk_disj" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam2 (solver_in, expr_list_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Allocate for local variables */
  CAMLlocal2 (head, expr_in);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Empty vector for list of expressions */
  std::vector<Expr> c;
  
  /* An expression in the disjunction */
  Expr* expr;

  /* Set to head of list */
  head = expr_list_in;

  /* Iterate list of expressions */
  while (head != Val_emptylist) 
    {

      /* Get element at head of list */
      expr_in = Field(head, 0);
      expr = cvc4_expr_val(expr_in);

      /* Push expression at head of list to end of vector */
      c.push_back(Expr(*expr));

      /* Continue with tail of list */
      head = Field(head, 1);
      
    }

  try {
    
    /* Create a disjunction */
    Expr expr = em->mkExpr(kind::OR, c);
    
    /* Copy expression into an OCaml value */
    res = copy_cvc4_expr(expr);
    
    /* Return type */
    CAMLreturn(res);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Add a formula to the current context

   external cvc4_assert_formula : cvc4_solver -> cvc4_expr -> bool = "cvc4_assert_formula" 
   
 */
extern "C" CAMLprim value cvc4_assert_formula(value solver_in, value expr_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_assert_formula";
#endif
  
  /* Declare parameters */
  CAMLparam2 (solver_in, expr_in);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get SMT engine */
  SmtEngine* smt = (SmtEngine*) Field(solver_in, smt_field);

  /* Get CVC4 expression from value */
  Expr* f = cvc4_expr_val(expr_in);

#ifdef DEBUG
  std::cerr << Expr::setlanguage(language::output::LANG_SMTLIB_V2) << *f << std::endl;
#endif
  
  try {

    /* Assert formula and get result */
    Result r = smt->assertFormula(*f);
  
    /* Check if context has become unsatisfiable 

       FIXME: When would assertFormula return unsat? It returns
       unknown on (assert false). But then we don't want a full check
       on every assert */
    if (r.isSat() == Result::UNSAT) { 
      
      /* Return false */
      CAMLreturn(Val_false);
      
    } else { 
      
      /* Return true */
      CAMLreturn(Val_true);
      
    }
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }
  
}


/* Check satisfiability of current context 

   external cvc4_check_sat : cvc4_solver -> cvc4_sat_result = "cvc4_check_sat" 
   
 */
extern "C" CAMLprim value cvc4_check_sat(value solver_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_check_sat" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam1 (solver_in);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get SMT engine */
  SmtEngine* smt = (SmtEngine*) Field(solver_in, smt_field);

  try {
    
    /* Check satisfiability of context */
    Result r = smt->checkSat();

#ifdef DEBUG
    std::cerr << r << std::endl;
#endif

    if (r.asSatisfiabilityResult() == Result::SAT) {

	/* Return satisfiability status as OCaml integer */
	CAMLreturn(Val_SAT);

    } else if (r.asSatisfiabilityResult() == Result::UNSAT) {
      
      /* Return satisfiability status as OCaml integer */
      CAMLreturn(Val_UNSAT);
      
    } else {
      
      /* Return satisfiability status as OCaml integer */
      CAMLreturn(Val_SAT_UNKNOWN);
      
    }
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }
  
}


/* Check validity of the expression by asserting its negation 

   external cvc4_query : cvc4_solver -> cvc4_expr -> cvc4_validity_result = "cvc4_query" 
   
 */
extern "C" CAMLprim value cvc4_query(value solver_in, value expr_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_query" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam2 (solver_in, expr_in);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get SMT engine */
  SmtEngine* smt = (SmtEngine*) Field(solver_in, smt_field);

  /* Get expresssion */
  Expr* expr = cvc4_expr_val(expr_in);

  try {
    
    /* Check satisfiability of context */
    Result r = smt->query(*expr);

#ifdef DEBUG
    std::cerr << r << std::endl;
#endif

    if (r.asValidityResult() == Result::VALID) {

	/* Return satisfiability status as OCaml integer */
	CAMLreturn(Val_VALID);

    } else if (r.asValidityResult() == Result::INVALID) {
      
      /* Return satisfiability status as OCaml integer */
      CAMLreturn(Val_INVALID);
      
    } else {
      
      /* Return satisfiability status as OCaml integer */
      CAMLreturn(Val_VALIDITY_UNKNOWN);
      
    }
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Get the value of a literal

   external cvc4_literal_value : cvc4_solver -> cvc4_expr -> lbool = "cvc4_literal_value" 
   
 */
extern "C" CAMLprim value cvc4_literal_value(value solver_in, value lit_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_literal_value" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam2 (solver_in, lit_in);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get SMT engine */
  SmtEngine* smt = (SmtEngine*) Field(solver_in, smt_field);

  /* Get CVC4 expression from value */
  Expr* f = cvc4_expr_val(lit_in);

  try {
    
    /* Check that result of last command was satisfiable */
    if (smt->getStatusOfLastCommand().asSatisfiabilityResult() != Result::SAT) {
    
      /* Cannot get value if not satisfiable */
      caml_failwith("literal_value: not satisfiable");

    }

    /* Check that type of expression is boolean */
    if (f->getType() != em->booleanType()) {
      
      /* Cannot get value of non-boolean expression */
      caml_invalid_argument("literal_value: not a Boolean");
      
    }
    
    /* Get assigned value to expression */
    Expr v = smt->getValue(*f);
    
    if (v == em->mkConst(true)) {
      
      /* Return l_True */
      CAMLreturn(Val_l_True);
      
    } else if (v == em->mkConst(false)) {
      
      /* Return l_False */
      CAMLreturn(Val_l_False);
      
    } else {
      
      /* Return l_Undef */
      CAMLreturn(Val_l_Undef);
      
    }
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}
  
  
/* Get the value of a literal

   external cvc4_literal_value : cvc4_solver -> cvc4_expr -> lbool = "cvc4_literal_value" 
   
 */
extern "C" CAMLprim value cvc4_literal_value_simplify(value solver_in, value lit_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_literal_value_simplify" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam2 (solver_in, lit_in);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get SMT engine */
  SmtEngine* smt = (SmtEngine*) Field(solver_in, smt_field);

  /* Get CVC4 expression from value */
  Expr* f = cvc4_expr_val(lit_in);

  try {

    /* Check that result of last command was satisfiable */
    if (smt->getStatusOfLastCommand().asSatisfiabilityResult() != Result::SAT) {
    
      /* Cannot get value if not satisfiable */
      caml_failwith("literal_value_simplify: not satisfiable");

    }
    
    /* Check that type of expression is boolean */
    if (f->getType() != em->booleanType()) {
      
      /* Cannot get value of non-boolean expression */
      caml_invalid_argument("literal_value_simplify: not Boolean");
      
    }
    
    /* Simplify expression 

       This should turn a Boolean expression either to true or false */
    Expr v = smt->simplify(*f);
    
#ifdef DEBUG
    std::cerr << *f << " simplified to " << v << std::endl;
#endif
    
    if (v == em->mkConst(true)) {
      
      /* Return l_True */
      CAMLreturn(Val_l_True);
      
    } else { 
      
      /* Return l_False */
      CAMLreturn(Val_l_False);
      
    }
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }
  
}


/* Push current context to next level

   external cvc4_push : cvc4_solver -> unit = "cvc4_push" 
   
 */
extern "C" CAMLprim value cvc4_push(value solver_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_push" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam1 (solver_in);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get SMT engine */
  SmtEngine* smt = (SmtEngine*) Field(solver_in, smt_field);

  /* Get number of previous pushes */
  int stack_level = (int) Field(solver_in, stack_level_field);

  try {

    /* Push context */
    smt->push();

    /* Increment number of context pushes */
    stack_level++;

    /* Store number of context pushes */
    Store_field(solver_in, stack_level_field, (value) stack_level); 
    
    /* Return unit */
    CAMLreturn(Val_unit);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Pop current context to previous level

   external cvc4_pop : cvc4_solver -> unit = "cvc4_pop" 
   
 */
extern "C" CAMLprim value cvc4_pop(value solver_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_pop" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam1 (solver_in);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get SMT engine */
  SmtEngine* smt = (SmtEngine*) Field(solver_in, smt_field);

  /* Get number of previous pushes */
  int stack_level = (int) Field(solver_in, stack_level_field);

  try {

    /* Pop context */
    smt->pop();
    
    /* Decrement number of context pushes */
    stack_level--;

    /* Store number of context pushes */
    Store_field(solver_in, stack_level_field, (value) stack_level); 

    /* Return unit */
    CAMLreturn(Val_unit);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Pop current context to given level

   external cvc4_pop_to : cvc4_solver -> unit = "cvc4_pop_to" 
   
 */
extern "C" CAMLprim value cvc4_pop_to(value solver_in, value stack_level_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_pop_to" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam1 (solver_in);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get SMT engine */
  SmtEngine* smt = (SmtEngine*) Field(solver_in, smt_field);

  /* Get number of previous pushes */
  int stack_level = (int) Field(solver_in, stack_level_field);

  /* Cannot pop to negative stack level */
  if (Int_val(stack_level_in) < 0)
   
    /* Throw exception */
    caml_invalid_argument("pop_to: cannot pop to negative stack level");
  
  /* Cannot pop to higher than current stack level */
  if (Int_val(stack_level_in) > stack_level)
  
    /* Throw exception */
    caml_invalid_argument("pop_to: cannot pop to a higher stack level");

  try {

    /* Repeat until stack level is at given level */
    while (Int_val(stack_level_in) < stack_level) {
      
#ifdef DEBUG
      std::cerr << "cvc4_pop" << std::endl;
#endif
  
      /* Pop context */
      smt->pop();
      
      /* Decrement number of context pushes */
      stack_level--;
      
    }
    
    /* Store number of context pushes */
    Store_field(solver_in, stack_level_field, Int_val(stack_level_in)); 
    
    /* Return unit */
    CAMLreturn(Val_unit);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Get current context level 

   external cvc4_get_stack_level : cvc4_solver -> int = "cvc4_get_stack_level" 
   
 */
extern "C" CAMLprim value cvc4_get_stack_level(value solver_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_get_stack_level" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam1 (solver_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Get expresssion mananger */
  ExprManager* em = (ExprManager*) Field(solver_in, em_field);

  /* Get SMT engine */
  SmtEngine* smt = (SmtEngine*) Field(solver_in, smt_field);

  /* Get number of previous pushes */
  int stack_level = (int) Field(solver_in, stack_level_field);

  /* Get current context level as OCaml integer */
  res = Val_int(stack_level);
  
  /* Return context level */
  CAMLreturn(res);

}


/* Return a string representation of the type 

   external cvc4_type_to_string : cvc4_type -> string = "cvc4_type_to_string" 

 */
extern "C" CAMLprim value cvc4_type_to_string(value type_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_type_to_string" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam1 (type_in);

  /* Allocate for a custom datatype for type */
  CAMLlocal1 (res);

  /* Get CVC4 type from value */
  Type* t = cvc4_type_val(type_in);

  try {

    /* Get string representation of type */
    std::string str = t->toString();
    
    /* Convert string to char* */
    const char* c = str.c_str();
    
    /* Copy char* to OCaml datatype */
    res = caml_copy_string (c);

    /* Return string representation of type */
    CAMLreturn(res);

  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Return a string representation of the expression

   external cvc4_expr_to_string : cvc4_expr -> string = "cvc4_expr_to_string" 

 */
extern "C" CAMLprim value cvc4_expr_to_string(value expr_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_expr_to_string: ";
#endif
  
  /* Declare parameters */
  CAMLparam1 (expr_in);

  /* Allocate for a custom datatype for expression */
  CAMLlocal1 (res);

  /* Get CVC4 expression from value */
  Expr* e = cvc4_expr_val(expr_in);

  try {

    /* Get string representation of type */
    std::string str = e->toString();
    
    /* Convert string to char* */
    const char* c = str.c_str();
    
    /* Copy char* to OCaml datatype */
    res = caml_copy_string (c);
    
    /* Return string representation of expression */
    CAMLreturn(res);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Return a string representation of the function type

   external cvc4_fun_type_to_string : cvc4_fun_type -> string = "cvc4_fun_type_to_string" 

 */
extern "C" CAMLprim value cvc4_fun_type_to_string(value fun_type_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_fun_type_to_string" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam1 (fun_type_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Get CVC4 expression from value */
  Expr* e = cvc4_expr_val(fun_type_in);

  try {

    /* Get string representation of type */
    std::string str = e->toString();

    /* Convert string to char* */
    const char* c = str.c_str();

    /* Copy char* to OCaml datatype */
    res = caml_copy_string (c);
    
    /* Return string representation of expression */
    CAMLreturn(res);

  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Return a string representation of the predicate type

   external cvc4_pred_type_to_string : cvc4_pred_type -> string = "cvc4_pred_type_to_string" 

 */
extern "C" CAMLprim value cvc4_pred_type_to_string(value pred_type_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_pred_type_to_string" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam1 (pred_type_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Get CVC4 expression from value */
  Expr* e = cvc4_expr_val(pred_type_in);

  try {

    /* Get string representation of type */
    std::string str = e->toString();
    
    /* Convert string to char* */
    const char* c = str.c_str();
    
    /* Copy char* to OCaml datatype */
    res = caml_copy_string (c);
    
    /* Return string representation of expression */
    CAMLreturn(res);

  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Get a hash for the expression

   external cvc4_hash_expr : cvc4_expr -> int = "cvc4_hash_expr" 
   
 */
extern "C" CAMLprim value cvc4_hash_expr(value expr_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_hash_expr" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam1 (expr_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Get expresssion */
  Expr* expr = cvc4_expr_val(expr_in);

  try {

    /* Get ID of expression */
    res = Val_int(expr->getId());

    /* Return ID as hash */
    CAMLreturn(res);
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


/* Structural comparison of expressions

   external cvc4_compare_expr : cvc4_expr -> cvc4_expr -> int = "cvc4_compare_expr" 
   
 */
extern "C" CAMLprim value cvc4_compare_expr(value expr1_in, value expr2_in)
{
  
#ifdef DEBUG
  std::cerr << "cvc4_compare_expr" << std::endl;
#endif
  
  /* Declare parameters */
  CAMLparam2 (expr1_in, expr2_in);

  /* Allocate for result */
  CAMLlocal1 (res);

  /* Get first expresssion */
  Expr* expr1 = cvc4_expr_val(expr1_in);

  /* Get second expresssion */
  Expr* expr2 = cvc4_expr_val(expr2_in);

  try {
    
    /* First expression is greater? */
    if (*expr1 > *expr2) {
      
      /* Return 1 */
      CAMLreturn(Val_int(1));
      
      /* Second expression is greater? */
    } else if (*expr1 < *expr2) {
      
      /* Return -1 */
      CAMLreturn(Val_int(-1));
      
      /* Expressions are equal */
    } else {
      
      /* Return 0 */
      CAMLreturn(Val_int(0));
      
  }
    
  } catch(Exception& e) {
    
    /* Throw OCaml exception */
    caml_failwith(e.what());
    
  }

}


