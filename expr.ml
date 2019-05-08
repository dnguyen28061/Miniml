(*
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions
 *)

type unop =
  | Negate
;;

type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
;;

type varid = string ;;

type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;

(*......................................................................
  Manipulation of variable names (varids)
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars :  varidset -> varidset -> bool
   Test to see if two sets of variables have the same elements (for
   testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list : string list -> varidset
   Generate a set of variable names from a list of strings (for
   testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;

(* free_vars : expr -> varidset
   Return a set of the variable names that are free in expression
   exp *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var x -> SS.add x SS.empty
  | Num _ | Bool _ | Raise | Unassigned -> SS.empty
  | Unop (_, y) -> free_vars y
  | Binop (_, x, y) -> SS.union (free_vars x) (free_vars y)
  | Conditional (x, y, z) -> SS.union (free_vars x)
                           (SS.union (free_vars y) (free_vars z))
  | Fun (var, body) -> SS.remove var (free_vars body)
  | Let (var, e1, e2) -> SS.union (SS.remove var (free_vars e2)) (free_vars e1)
  | Letrec (var, e1, e2) -> SS.union (SS.remove var (free_vars e2)) (free_vars e1)
  | App (e1, e2) -> SS.union (free_vars e1) (free_vars e2)  ;;

(* new_varname : unit -> varid
   Return a fresh variable, constructed with a running counter a la
   gensym. Assumes no variable names use the prefix "var". (Otherwise,
   they might accidentally be the same as a generated variable name.) *)

let new_varname : unit -> varid =
  let x = ref ~-1 in
  fun () ->
  x := !x + 1;
  "var" ^ (string_of_int !x) ;;

(*......................................................................
  Substitution

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst : varid -> expr -> expr -> expr
   Substitute repl for free occurrences of var_name in exp *)
exception Impossible_case
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
   if SS.mem var_name (free_vars exp)
   then match exp with
  | Var _-> repl
  | Num _ | Bool _ -> raise Impossible_case
  | Unop (op, e) -> Unop(op, subst var_name repl e)
  | Binop (op, x, y) -> Binop(op, (subst var_name repl x), (subst var_name repl y))
  | Conditional (e1, e2, e3) -> Conditional((subst var_name repl e1),
                                            (subst var_name repl e2),
                                            (subst var_name repl e3))
  (* Case in which y is in the FV(P), so we must create new var *)
  | Fun (var, e1) -> if SS.mem var (free_vars repl)
                     then let new_var = new_varname () in
                     (* In Q, we must substitute twice, once for new var
                        and again for original sub, so this is first sub *)
                      let first_sub = subst var (Var new_var) e1 in
                      Fun(new_var, (subst var_name repl first_sub))
                     else Fun(var, (subst var_name repl e1))
 (* Let  rec is slightly different from let *)
  | Let (var, e1, e2) ->
      (* Case where let statement overrides the substitution *)
      if var = var_name then Let(var, (subst var_name repl e1), e2)
      (* Case where y is in FV(P) and x neq y *)
      else if (SS.mem var (free_vars repl))
        then let new_var = new_varname () in
        let first_sub = subst var (Var new_var) e2 in
        Let(new_var, (subst var_name repl e1), (subst  var_name repl first_sub))
      (* Last case where y is not in FV(P) *)
      else
      Let(var, (subst var_name repl e1), (subst var_name repl e2))
  | Letrec (var, e1, e2) ->
      if var = var_name then exp
      else if (SS.mem var (free_vars repl))
        then let new_var = new_varname () in
        let sub_def_new_var = subst var (Var new_var) e1 in
        let sub_body_new_var = subst var (Var new_var) e2 in
        let sub_def_repl = subst var_name repl sub_def_new_var in
        let sub_body_repl = subst var_name repl sub_body_new_var in
        Letrec(new_var, sub_def_repl, sub_body_repl)
      else Letrec(var, (subst var_name repl e1), (subst var_name repl e2))
  | Raise | Unassigned -> exp
  | App (e1, e2) -> App(subst var_name repl e1, (subst var_name repl e2))
   else exp ;;

(*......................................................................
  String representations of expressions
 *)


(* f : expr -> string
   Returns a concrete syntax string representation of the expr *)

(* Function that wraps a string in parentheses *)
let paren (wrapped : string) : string =
  "(" ^ wrapped ^ ")"
let rec exp_to_concrete_string (exp : expr) : string =
    let f = exp_to_concrete_string in
    match exp with
    | Var x -> paren x
    | Num x -> paren (string_of_int x)
    | Bool x -> paren (string_of_bool x)
    | Unop (_, y) -> paren (" ~ eva" ^ (f y))
    | Binop (x, y, z) ->
        (match x with (* Let symbol = "operator" in helper left, symbol, helper right.*)
          | Plus -> paren (f y ^ " + " ^ f z)
          | Minus -> paren (f y ^ " - " ^ f z)
          | Times -> paren (f y ^ " * " ^ f z)
          | Equals -> paren (f y ^ " = " ^ f z)
          | LessThan -> paren(f y ^ " < " ^ f z))

    | Conditional (x, y, z) -> paren("if " ^ f x ^ " then " ^ f y ^ " else " ^ f z)
    | Fun (x, y) -> paren("fun " ^ (x) ^ " -> " ^ f y)
    | Let (x, y, z) -> paren("let " ^ (x) ^ " = " ^ f y ^ " in " ^ f z)
    | Letrec (x, y, z) -> paren("let rec " ^ (x) ^ " = " ^ f y ^ " in " ^ f z)
    | Raise -> "Raise"
    | Unassigned -> "Unassigned"
    | App (x, y) -> paren(f x ^ " " ^ f y)

(* exp_to_abstract_string : expr -> string
   Returns a string representation of the abstract syntax of the expr *)
let rec exp_to_abstract_string (exp : expr) : string =
    let f = exp_to_abstract_string in
    match exp with
    | Var x -> "Var" ^ paren x
    | Num x ->  "Num" ^ paren(string_of_int x)
    | Bool x -> "Bool" ^ paren(string_of_bool x)
    | Unop (x, y) -> "Unop" ^ paren("Negate" ^ paren(f y))
    | Binop (x, y, z) ->
        (match x with (* Let symbol = "operator" in helper left, symbol, helper right.*)
          | Plus -> "Binop" ^ paren("Plus" ^ ", " ^ f y ^ ", " ^ (f z))
          | Minus -> "Binop" ^ paren("Minus" ^ ", " ^ f y ^ ", " ^ (f z))
          | Times -> "Binop" ^  paren("Times" ^ ", " ^ f y ^ ", " ^ (f z))
          | Equals -> "Binop" ^ paren("Equals" ^ ", " ^ f y ^ ", " ^ (f z))
          | LessThan -> "Binop" ^ paren("LessThan" ^ ", " ^ f y ^ ", " ^ (f z)))
    | Conditional (x, y, z) -> "Conditional" ^ paren (f x ^ ", " ^ f y ^ ", " ^ f z)
    | Fun (x, y) -> "Fun" ^ paren (x ^ ")" ^ ", " ^ f y)
    | Let (x, y, z) -> "Let" ^ paren (x ^ ")" ^ ", " ^ f y ^ ", " ^ f z)
    | Letrec (x, y, z) -> "Letrec" ^ paren (x ^ ", " ^ f y ^ ", " ^ f z)
    | Raise -> "Raise"
    | Unassigned -> "Unassigned"
    | App (x, y) -> "App" ^ paren (f x ^ ", " ^ f y) ;;
