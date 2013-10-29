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

type cvc4_solver

type cvc4_type

type cvc4_fun_type

type cvc4_pred_type

type cvc4_expr

type lbool =
  | L_True
  | L_False
  | L_Undef

type cvc4_sat_result =
  | UNSAT
  | SAT
  | SAT_UNKNOWN

type cvc4_validity_result =
  | INVALID
  | VALID
  | VALIDITY_UNKNOWN

external cvc4_create_smt_engine : bool -> int -> cvc4_solver = "cvc4_create_smt_engine" 

external cvc4_get_integer_type : cvc4_solver -> cvc4_type = "cvc4_get_integer_type" 

external cvc4_get_bool_type : cvc4_solver -> cvc4_type = "cvc4_get_bool_type" 

external cvc4_mk_type : cvc4_solver -> string -> cvc4_type = "cvc4_mk_type" 

external cvc4_get_true_expr : cvc4_solver -> cvc4_expr = "cvc4_get_true_expr" 

external cvc4_get_false_expr : cvc4_solver -> cvc4_expr = "cvc4_get_false_expr" 

external cvc4_mk_var : cvc4_solver -> string -> cvc4_type -> cvc4_expr = "cvc4_mk_var" 

external cvc4_mk_not : cvc4_solver -> cvc4_expr -> cvc4_expr = "cvc4_mk_not"

external cvc4_negate : cvc4_solver -> cvc4_expr -> cvc4_expr = "cvc4_negate"

external cvc4_mk_function_type : cvc4_solver -> string -> cvc4_type list -> cvc4_type -> cvc4_fun_type = "cvc4_mk_function_type" 

external cvc4_mk_function_expr : cvc4_solver -> cvc4_fun_type -> cvc4_expr list -> cvc4_expr = "cvc4_mk_function_expr" 

external cvc4_mk_predicate_type : cvc4_solver -> string -> cvc4_type list -> cvc4_pred_type = "cvc4_mk_predicate_type" 

external cvc4_mk_predicate_expr : cvc4_solver -> cvc4_pred_type -> cvc4_expr list -> cvc4_expr = "cvc4_mk_predicate_expr" 

external cvc4_mk_equation : cvc4_solver -> cvc4_expr -> cvc4_expr -> cvc4_expr = "cvc4_mk_equation" 

external cvc4_mk_disj : cvc4_solver -> cvc4_expr list -> cvc4_expr = "cvc4_mk_disj" 

external cvc4_assert_formula : cvc4_solver -> cvc4_expr -> bool = "cvc4_assert_formula" 

external cvc4_check_sat : cvc4_solver -> cvc4_sat_result = "cvc4_check_sat" 

external cvc4_query : cvc4_solver -> cvc4_expr -> cvc4_validity_result = "cvc4_query" 

external cvc4_literal_value : cvc4_solver -> cvc4_expr -> lbool = "cvc4_literal_value" 

external cvc4_push : cvc4_solver -> unit = "cvc4_push" 

external cvc4_pop : cvc4_solver -> unit = "cvc4_pop" 

external cvc4_pop_to : cvc4_solver -> int -> unit = "cvc4_pop_to" 

external cvc4_get_stack_level : cvc4_solver -> int = "cvc4_get_stack_level" 

external cvc4_fun_type_to_string : cvc4_fun_type -> string = "cvc4_fun_type_to_string" 

external cvc4_pred_type_to_string : cvc4_pred_type -> string = "cvc4_pred_type_to_string" 

external cvc4_type_to_string : cvc4_type -> string = "cvc4_type_to_string" 

external cvc4_expr_to_string : cvc4_expr -> string = "cvc4_expr_to_string" 

external cvc4_hash_expr : cvc4_expr -> int = "cvc4_hash_expr" 

external cvc4_compare_expr : cvc4_expr -> cvc4_expr -> int = "cvc4_compare_expr" 

let create_cvc4_solver ?(rlimit = 0) m = cvc4_create_smt_engine m rlimit 

let get_integer_type s = cvc4_get_integer_type s

let get_bool_type s = cvc4_get_bool_type s

let mk_type s t = cvc4_mk_type s t

let get_true_expr s = cvc4_get_true_expr s

let get_false_expr s = cvc4_get_false_expr s
  
let mk_var s v t = cvc4_mk_var s v t

let mk_not s e = cvc4_mk_not s e

let negate s e = cvc4_negate s e

let mk_function_type s f d r = cvc4_mk_function_type s f d r

let mk_function_expr s f a = cvc4_mk_function_expr s f a

let mk_predicate_type s p d = cvc4_mk_predicate_type s p d

let mk_predicate_expr s p a = cvc4_mk_predicate_expr s p a

let mk_equation s l r = cvc4_mk_equation s l r 

let mk_disj s c = cvc4_mk_disj s c

let assert_formula s f = cvc4_assert_formula s f

let check_sat s = cvc4_check_sat s

let query s e = cvc4_query s e

let literal_value s l = cvc4_literal_value s l

let push s = cvc4_push s

let pop s = cvc4_pop s

let pop_to s l = cvc4_pop_to s l

let get_stack_level s = cvc4_get_stack_level s

let type_to_string t = cvc4_type_to_string t

let fun_type_to_string t = cvc4_fun_type_to_string t

let pred_type_to_string t = cvc4_pred_type_to_string t

let expr_to_string e = cvc4_expr_to_string e

let lbool_to_string = function 
  | L_True -> "l_True"
  | L_False -> "l_False"
  | L_Undef -> "l_Undef"

let lbool_to_bool_option = function 
  | L_True -> Some true
  | L_False -> Some false 
  | L_Undef -> None

let sat_result_to_string = function
  | UNSAT -> "UNSAT"
  | SAT -> "SAT"
  | SAT_UNKNOWN -> "SAT_UNKNOWN"

let validity_result_to_string = function
  | INVALID -> "INVALID"
  | VALID -> "VALID"
  | VALIDITY_UNKNOWN -> "VALIDITY_UNKNOWN"

let hash_expr e = cvc4_hash_expr e

let compare_expr e1 e2 = cvc4_compare_expr e1 e2

