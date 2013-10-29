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

let main () =
  
  let s = Cvc4.create_cvc4_solver true in

  let t1 = Cvc4.get_true_expr s in

  let t = Cvc4.get_true_expr s in

  Format.printf "%s %s %d (%d %d)@." (Cvc4.expr_to_string t) (Cvc4.expr_to_string t1) (compare t t1) (Hashtbl.hash t) (Hashtbl.hash t1);

  let t = Cvc4.get_false_expr s in

  Gc.full_major ();

  Format.printf "%s %d (%d)@." (Cvc4.expr_to_string t1) (compare t1 t) (Hashtbl.hash t1);

  let ty_default = Cvc4.mk_type s "default" in

  Format.printf "%s@." (Cvc4.type_to_string ty_default);

  let ty_f = Cvc4.mk_type s "f" in

  Format.printf "%s@." (Cvc4.type_to_string ty_f);

  let ty_default' = Cvc4.mk_type s "default" in

  Format.printf "%s@." (Cvc4.type_to_string ty_default');

  let t_a = Cvc4.mk_var s "a" ty_default in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_a) (Cvc4.hash_expr t_a);

  let t_b = Cvc4.mk_var s "b" ty_default in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_b) (Cvc4.hash_expr t_b);

  let t_b' = Cvc4.mk_var s "b" ty_default' in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_b') (Cvc4.hash_expr t_b');

  Format.printf "%d@." (Cvc4.compare_expr t_b t_b');

  let sym_f = Cvc4.mk_function_type s "f" [ty_default] ty_default in

  Format.printf "%s@." (Cvc4.fun_type_to_string sym_f);

  let sym_f' = Cvc4.mk_function_type s "f" [ty_default'] ty_default' in 

  Format.printf "%s@." (Cvc4.fun_type_to_string sym_f');

  let t_fa = Cvc4.mk_function_expr s sym_f [t_a] in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_fa) (Cvc4.hash_expr t_fa);

  let t_fa' = Cvc4.mk_function_expr s sym_f' [t_a] in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_fa') (Cvc4.hash_expr t_fa');

  Format.printf "%d@." (Cvc4.compare_expr t_fa t_fa');

  let t_fb = Cvc4.mk_function_expr s sym_f [t_b] in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_fb) (Cvc4.hash_expr t_fb);

  let t_fb' = Cvc4.mk_function_expr s sym_f [t_b'] in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_fb') (Cvc4.hash_expr t_fb');

  let sym_P = Cvc4.mk_predicate_type s "P" [ty_default; ty_default] in

  Format.printf "%s@." (Cvc4.pred_type_to_string sym_P);

  let sym_P' = Cvc4.mk_predicate_type s "P" [ty_default] in

  Format.printf "%s@." (Cvc4.pred_type_to_string sym_P');

  let t_Pa = Cvc4.mk_predicate_expr s sym_P [t_a; t_a] in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_Pa) (Cvc4.hash_expr t_Pa);

  let t_P'a = Cvc4.mk_predicate_expr s sym_P' [t_a] in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_P'a) (Cvc4.hash_expr t_P'a);

  Format.printf "%d@." (Cvc4.compare_expr t_Pa t_P'a);

  let t_Pfa = Cvc4.mk_predicate_expr s sym_P [t_fa; t_fa] in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_Pfa) (Cvc4.hash_expr t_Pfa);

  let t_Pb = Cvc4.mk_predicate_expr s sym_P [t_b; t_b] in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_Pb) (Cvc4.hash_expr t_Pb);

  let t_Pfb = Cvc4.mk_predicate_expr s sym_P [t_fb; t_fb] in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_Pfb) (Cvc4.hash_expr t_Pfb);

  let t_nPa = Cvc4.mk_not s t_Pa in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_nPa) (Cvc4.hash_expr t_nPa);

  let t_nPb = Cvc4.mk_not s t_Pb in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_nPb) (Cvc4.hash_expr t_nPb);

  let t_eqab = Cvc4.mk_equation s t_a t_b in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_eqab) (Cvc4.hash_expr t_eqab);

  let t_eqba = Cvc4.mk_equation s t_b t_a in

  Format.printf "%s (%d)@." (Cvc4.expr_to_string t_eqba) (Cvc4.hash_expr t_eqba);

  Format.printf "%s (%d)@." (Cvc4.expr_to_string (Cvc4.mk_disj s [t_Pfa; t_nPa])) (Cvc4.hash_expr (Cvc4.mk_disj s [t_Pfa; t_nPa]));

;;

main ()

;;
