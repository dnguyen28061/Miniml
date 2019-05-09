open Expr

let test () =

  (* free_vars testing *)
   assert (same_vars (vars_of_list ["x"]) (free_vars (Var("x"))) = true);
   assert (same_vars (vars_of_list [])  (free_vars (Bool(true))) = true);
   assert (same_vars (vars_of_list [])  (free_vars (Raise)) = true);
   assert (same_vars (vars_of_list [])  (free_vars (Unassigned)) = true);
   assert (same_vars (vars_of_list ["x"; "y"; "z"])
          (free_vars(Conditional(Var("x"),Var("y"),Var("z")))) = true);
   assert (same_vars (vars_of_list ["y"])
          (free_vars(Fun("x",Binop(Plus,Var("x"),Var("y"))))) = true);
   assert (same_vars (vars_of_list ["y"])
          (free_vars(Let("x", Var("y"),Fun("x",Var("y"))))) = true);
   assert (same_vars (vars_of_list["x";"y"])
          (free_vars (App(Fun("z",Conditional(Var("x"),Var("y"),Var("z"))),
           Num(2)))) = true);

   (* fun x -> x*)
   let case_1_fun = Fun("x", Var("x")) in
   (* fun y  -> x *)
   let case_2_fun = Fun("y", Var("x")) in
   assert (subst "x" (Num 2) case_1_fun = Fun("x", Var("x")));
   (* [x -> 2], fun y -> x = fun y -> 2 *)
   assert (subst "x" (Num 2) case_2_fun = Fun("y", Num(2)));
   (* [x -> y], fun y -> x = fun (new_var) -> y *)
   assert(subst "x" (Var "y") case_2_fun = Fun("var0", Var("y")));
   (* [z -> 2], fun y -> x = fun y -> x *)
   assert (subst "z" (Num 2) case_2_fun = case_2_fun);
   (* [x -> 2], (~- x) = ~-2*)
   assert (subst "x" (Num 2) (Unop(Negate, Var("x"))) = Unop(Negate,(Num(2))));
   (* subst case when let overrides
      [x -> 2] Let x = 2 in x = Let x = 2 in x *)
   assert (subst "x" (Num 2) (Let(("x"), Num(2), Var("x"))) =
          (Let(("x"), Num(2), Var("x"))));
   (* subst case when let doesn't override
      [x -> 2] Let y = 2 in x + y -> Let y = 2 in 2 + y *)
   assert (subst "x" (Num 2) (Let("y", Num(2), Binop(Plus,Var("x"), Var("y")))) =
          Let("y", Num(2), Binop(Plus, Num(2), Var("y"))));
   (* Subst case when making a fresh variable
      [x -> y] Let y = 2 in y + x -> Let z = 2 in z + y *)
   assert(subst "x" (Var("y")) (Let("y", Num(2), Binop(Plus,Var("y"), Var("x")))) =
          Let("var1", Num(2), Binop(Plus,Var("var1"),Var("y"))));
 (* Letrec where substitution is overwritten *)
   assert (subst "f" (Num(2)) (Letrec("f", Var("f"), Var("f"))) = (Letrec("f", Var("f"), Var("f"))));
   (* Letrec where we replace wth new var *)
   assert (subst "x" (Var("f")) (Letrec("f", Var("g"), Binop(Plus,Var("f"),Var("x")))) =
          (Letrec(("var2"), Var("g"), Binop(Plus,Var("var2"),Var("f")))));
   (* Letrec, where x is not equal to y and y is not in FV(P) *)
   assert (subst "x" (Var("y")) (Letrec("f", Var("x"), Var("x"))) =
           Letrec(("f"), Var("y"), Var("y")))





;;
test ();;
