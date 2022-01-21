(*
ADAM Pauline
TORIS Ugo
Groupe 21
*)

open Printf

(* Définitions de terme, test et programme *)
type term = 
 | Const of int
 | Var of int
 | Add of term * term
 | Mult of term * term

type test = 
 | Equals of term * term
 | LessThan of term * term

let tt = Equals (Const 0, Const 0)
let ff = LessThan (Const 0, Const 0)
 
type program = {nvars : int; 
                inits : term list; 
                mods : term list; 
                loopcond : test; 
                assertion : test}

let x n = "x" ^ string_of_int n

(* Question 1. Écrire des fonctions `str_of_term` et `str_of_test` qui
   convertissent des termes et des tests en chaînes de caractères du
   format SMTLIB.*)
let rec str_of_term t = 
  match t with
  |Const x -> string_of_int x
  |Var x -> "x" ^ (string_of_int x)
  |Add (t1,t2) -> "+ " ^ (str_of_term t1) ^  " " ^ (str_of_term t2)
  |Mult (t1,t2) -> "* " ^ (str_of_term t1) ^  " " ^ (str_of_term t2)
;;

let str_of_test t = 
  match t with
  |Equals(t1,t2) -> "(= " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"
  |LessThan(t1,t2) -> "(< " ^ (str_of_term t1) ^ " " ^ (str_of_term t2) ^ ")"
;;

let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s)

(* Question 2. Écrire une fonction str_condition qui prend une liste
   de termes t1, ..., tk et retourne une chaîne de caractères qui
   exprime que le tuple (t1, ..., tk) est dans l'invariant. *)
let str_condition l =

  let rec apply_str_cond l str =
    match l with
    | [] -> 
      if str = "" then
        failwith "Condition vide"
      else
        "(Invar"^str^")"
    | x::ll -> apply_str_cond ll (str^" "^(str_of_term x))
  in
  apply_str_cond l ""


(* Question 3. Écrire une fonction str_assert_for_all qui prend en
   argument un entier n et une chaîne de caractères s, et retourne
   l'expression SMTLIB qui correspond à la formule "forall x1 ... xk
   (s)".*)

let str_assert s = "(assert " ^ s ^ ")"

let str_assert_forall n s = 

let rec all_vars n compt =
  if n < compt then
    ""
  else
    "(x" ^ (string_of_int compt) ^ " Int)" ^ (all_vars n (compt + 1)) 
in
if (s = "") then
  str_assert ("(forall (" ^ all_vars n 1)
else 
  str_assert ("(forall (" ^ all_vars n 1 ^ ") (" ^ s ^ ")")
;;

(* Question 4. Nous donnons ci-dessous une définition possible de la
   fonction smt_lib_of_wa. Complétez-la en écrivant les définitions de
   loop_condition et assertion_condition. *)

let smtlib_of_wa p = 
  let declare_invariant n =
    "; synthèse d'invariant de programme\n"
    ^"; on déclare le symbole non interprété de relation Invar\n"
    ^"(declare-fun Invar (" ^ string_repeat "Int " n ^  ") Bool)" in


  let rec recupVar vars compt list=
    if compt > vars then list
    else
      recupVar vars (compt + 1) (list@[Var(compt)])
  in

  let rec print_mod m str=
    match m with
    | [] -> str
    | x::l -> print_mod l (str^"("^(str_of_term x)^") ")
  in
    

  let loop_condition p =
    "; la relation Invar est un invariant de boucle\n"
    ^(str_assert_forall p.nvars "")
    ^"\n(=> "
    ^"(and "^(str_condition (recupVar p.nvars 1 []))^" "^(str_of_test p.loopcond)^") "
    ^"(Invar "^(print_mod p.mods "")^")"
    ^")))"
    in

  let initial_condition p =
    "; la relation Invar est vraie initialement\n"
    ^str_assert (str_condition p.inits) in

  let oppositeTest t =
    match t with
    |Equals(t1,t2) -> Equals(t1,t2)
    |LessThan(t1,t2) -> 
      let a = int_of_string(str_of_term t2) in
      LessThan(Const(a-1), t1)
  in

  let assertion_condition p =
    "; l'assertion finale est vérifiée\n"
    ^(str_assert_forall p.nvars "")
    ^"\n(=> "
    ^"(and "^(str_condition (recupVar p.nvars 1 []))^" "^(str_of_test (oppositeTest p.loopcond))^") "
    ^(str_of_test p.assertion)
    ^")))"
    in

  let call_solver =
    "; appel au solveur\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n" in
    
  String.concat "\n" [declare_invariant p.nvars;
                      loop_condition p;
                      initial_condition p;
                      assertion_condition p;
                      call_solver]

let p1 = {nvars = 2;
          inits = [(Const 0) ; (Const 0)];
          mods = [Add ((Var 1), (Const 1)); Add ((Var 2), (Const 3))];
          loopcond = LessThan ((Var 1),(Const 3));
          assertion = Equals ((Var 2),(Const 9))}

(* Question 5. Vérifiez que votre implémentation donne un fichier
   SMTLIB qui est équivalent au fichier que vous avez écrit à la main
   dans l'exercice 1. Ajoutez dans la variable p2 ci-dessous au moins
   un autre programme test, et vérifiez qu'il donne un fichier SMTLIB
   de la forme attendue. *)

(*Soit p2 l'exemple de la video du projet*)
let p2 = {nvars = 2;
          inits = [(Const 0) ; (Const 1)];
          mods = [Add ((Var 1), (Const 2)); Add ((Var 2), (Const 1))];
          loopcond = LessThan ((Var 1),(Const 10));
          assertion = LessThan ((Var 2),(Const 10))}


let () = Printf.printf "%s" (smtlib_of_wa p2)