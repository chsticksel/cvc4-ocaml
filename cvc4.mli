(* OCaml bindings for CVC4

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
   
*)

(** OCaml bindings for CVC4 

    @author Christoph Sticksel *)

(** {1 Types} *)

(** A solver instance

    No finalization is done when values of this type are garbage
    collected, this is, the allocated memory is not freed. *)
type cvc4_solver

(** A type 

    Types can be compared with the polymorphic comparison function,
    but there is no hash function for types. *)
type cvc4_type

(** An uninterpreted function symbol 
    
    Expressions can be compared with the polymorphic comparison
    function and hashed with the polymorphic hash function. *)
type cvc4_fun_type

(** A predicate 
    
    Expressions can be compared with the polymorphic comparison
    function and hashed with the polymorphic hash function. *)
type cvc4_pred_type

(** An expression 
    
    Expressions can be compared with the polymorphic comparison
    function and hashed with the polymorphic hash function. *)
type cvc4_expr

(** A lifted Boolean value *)
type lbool =
  | L_True
  | L_False
  | L_Undef

(** Answer from a {!check_sat} call *)
type cvc4_sat_result =
  | UNSAT
  | SAT
  | SAT_UNKNOWN

(** Answer from a {!query} call *)
type cvc4_validity_result =
  | INVALID
  | VALID
  | VALIDITY_UNKNOWN

(** {1 Solver instances} *)

(** Create a new solver instance for the [QF_UF] theory

    Set the Boolean parameter to [true] to produce models. *)
val create_cvc4_solver : ?rlimit:int -> bool -> cvc4_solver

(** {1 Solver types}*)

(** Return the integer type *)
val get_integer_type : cvc4_solver -> cvc4_type

(** Return the Boolean type *)
val get_bool_type : cvc4_solver -> cvc4_type

(** Create an uninterpreted type or return the previously created
    uninterpreted type of the given name *)
val mk_type : cvc4_solver -> string -> cvc4_type


(** {1 Solver expressions} *)

(** Return the propositional constant true *)
val get_true_expr : cvc4_solver -> cvc4_expr

(** Return the propositional constant false *)
val get_false_expr : cvc4_solver -> cvc4_expr

(** Create a variable (a constant) or return the previously created
    variable of the given name *)
val mk_var : cvc4_solver -> string -> cvc4_type -> cvc4_expr

(** Negate an expression *)
val mk_not : cvc4_solver -> cvc4_expr -> cvc4_expr

(** Return the complement of the expression, avoiding double negations

    If the top symbol is a negation, return the expression under the
    negation; otherwise negate the expressoin. *)
val negate : cvc4_solver -> cvc4_expr -> cvc4_expr

(** Create an uninterpreted function symbol of the given type or
    return the previously created uninterpreted function symbol of the
    given name. The list of argument types must not be empty, use
    {!mk_var} to create uninterpreted constants.

    When returning a previously created function symbol, the given
    type is ignored, even if the type of the returned symbol does not
    match it. *)
val mk_function_type : cvc4_solver -> string -> cvc4_type list -> cvc4_type -> cvc4_fun_type

(** Create an uninterpreted function application *)
val mk_function_expr : cvc4_solver -> cvc4_fun_type -> cvc4_expr list -> cvc4_expr

(** Create an uninterpreted predicate symbol of the given type or
    return the previously created uninterpreted predicate symbol of the
    given name. The list of argument types must not be empty, use
    {!mk_var} to create propositional constants.

    When returning a previously created predicate symbol, the given
    type is ignored, even if the type of the returned symbol does not
    match it. *)
val mk_predicate_type : cvc4_solver -> string -> cvc4_type list -> cvc4_pred_type

(** Create an uninterpreted predicate *)
val mk_predicate_expr : cvc4_solver -> cvc4_pred_type -> cvc4_expr list -> cvc4_expr

(** Create an equation between two expressions *)
val mk_equation : cvc4_solver -> cvc4_expr -> cvc4_expr -> cvc4_expr

(** Create a disjunction between expressions *)
val mk_disj : cvc4_solver -> cvc4_expr list -> cvc4_expr

(** {1 Logical contexts} *)

(** Assert the expression in the context *)
val assert_formula : cvc4_solver -> cvc4_expr -> bool

(** Check satisfiability of the context *)
val check_sat : cvc4_solver -> cvc4_sat_result

(** Check validity of the expression in the context by asserting its
    negation and checking the context for satisfiability *)
val query : cvc4_solver -> cvc4_expr -> cvc4_validity_result

(** Return the Boolean value of the expression in the context

    There must have been at least on {!check_sat} or {!query} call
    before and the context must have be satisfiable or the queried
    expression must have been invalid. *)
val literal_value : cvc4_solver -> cvc4_expr -> lbool

(** Push a new scope level to the context *)
val push : cvc4_solver -> unit

(** Pop the most recent scope level from the context *)
val pop : cvc4_solver -> unit

(** Pop scope levels from the context until there are the given number
    of scope levels *)
val pop_to : cvc4_solver -> int -> unit

(** Return the current scope level *)
val get_stack_level : cvc4_solver -> int

(** {1 String representations} *)

(** Return a string representation of a type *)
val type_to_string : cvc4_type -> string

(** Return a string representation of an uninterpreted function symbol *)
val fun_type_to_string : cvc4_fun_type -> string

(** Return a string representation of an uninterpreted predicate symbol *)
val pred_type_to_string : cvc4_pred_type -> string

(** Return a string representation of an expression *)
val expr_to_string : cvc4_expr -> string

(** Return a string representation of an lifted Boolena value *)
val lbool_to_string : lbool -> string 

(** Return a string representation of a satisfiability result *)
val sat_result_to_string : cvc4_sat_result -> string 

(** Return a string representation of a validity result *)
val validity_result_to_string : cvc4_validity_result -> string 

(** {1 Utility functions} *)

(** Convert a lifted Boolean value to a [bool option] type *)
val lbool_to_bool_option : lbool -> bool option

(** Return a hash of an expression *)
val hash_expr : cvc4_expr -> int

(** Compare two expressions *)
val compare_expr : cvc4_expr -> cvc4_expr -> int
