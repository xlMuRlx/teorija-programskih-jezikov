module S = Syntax

let fresh_ty =
  let counter = ref 0 in
  fun () -> incr counter; S.ParamTy (S.Param !counter)


let rec infer_exp ctx = function
  | S.Var x ->
      List.assoc x ctx, []
  | S.Int _ ->
      S.IntTy, []
  | S.Bool _ ->
      S.BoolTy, []
  | S.Plus (e1, e2) | S.Minus (e1, e2) | S.Times (e1, e2) ->
      let t1, eqs1 = infer_exp ctx e1
      and t2, eqs2 = infer_exp ctx e2 in
      S.IntTy, [(t1, S.IntTy); (t2, S.IntTy)] @ eqs1 @ eqs2
  | S.Equal (e1, e2) | S.Less (e1, e2) | S.Greater (e1, e2) ->
      let t1, eqs1 = infer_exp ctx e1
      and t2, eqs2 = infer_exp ctx e2 in
      S.BoolTy, [(t1, S.IntTy); (t2, S.IntTy)] @ eqs1 @ eqs2
  | S.IfThenElse (e, e1, e2) ->
      let t, eqs = infer_exp ctx e
      and t1, eqs1 = infer_exp ctx e1
      and t2, eqs2 = infer_exp ctx e2 in
      t1, [(t, S.BoolTy); (t1, t2)] @ eqs @ eqs1 @ eqs2
  | S.Lambda (x, e) ->
      let a = fresh_ty () in
      let ctx' = (x, a) :: ctx in
      let t, eqs = infer_exp ctx' e in
      S.ArrowTy (a, t), eqs
  | S.RecLambda (f, x, e) ->
      let a = fresh_ty ()
      and b = fresh_ty () in
      let ctx' = (x, a) :: (f, S.ArrowTy (a, b)) :: ctx in
      let t, eqs = infer_exp ctx' e in
      S.ArrowTy (a, b), [(b, t)] @ eqs
  | S.Apply (e1, e2) ->
      let t1, eqs1 = infer_exp ctx e1
      and t2, eqs2 = infer_exp ctx e2
      and a = fresh_ty ()
      in
      a, [(t1, S.ArrowTy (t2, a))] @ eqs1 @ eqs2
  | S.Pair (e1, e2) ->
      let t1, eqs1 = infer_exp ctx e1
      and t2, eqs2 = infer_exp ctx e2 in
      S.ProdTy (t1, t2), eqs1 @ eqs2
  | S.Fst e ->
      let a = fresh_ty ()
      and b = fresh_ty () in
      let t, eqs = infer_exp ctx e in
      a, [(S.ProdTy (a, b), t)] @ eqs
  | S.Snd e ->
      let a = fresh_ty ()
      and b = fresh_ty () in
      let t, eqs = infer_exp ctx e in
      b, [(S.ProdTy (a, b), t)] @ eqs
  | S.Nil ->
      let a = fresh_ty () in
      S.ListTy a, []
  | S.Cons (e, es) ->
      let t, eqs1 = infer_exp ctx e
      and t2, eqs2 = infer_exp ctx es in
      S.ListTy t, [(S.ListTy t, t2)] @ eqs1 @ eqs2
  | S.Match (e, e1, x, xs, e2) ->
      let a = fresh_ty () in
      let t, eqs = infer_exp ctx e
      and t1, eqs1 = infer_exp ctx e1 in 
      let ctx' = (x, a) :: (xs, S.ListTy a) :: ctx in
      let t2, eqs2 = infer_exp ctx' e2 in
      t1, [(t1, t2); (t, S.ListTy a)] @ eqs @ eqs1 @ eqs2


let subst_equations sbst =
  (* Substitutes type parameters for types in equations. *)
  let subst_equation (t1, t2) = (S.subst_ty sbst t1, S.subst_ty sbst t2) in
  List.map subst_equation


let add_subst a t sbst =
  (* Adds a new substitution to the solution. *)
  let subst_subst (a', t') = (a', S.subst_ty [(a, t)] t') in
  (a, t) :: List.map subst_subst sbst



let rec occurs a = function
  (* Checks if a given type parameter occurs in the type *)
  | S.ParamTy a' -> a = a'
  | S.IntTy | S.BoolTy -> false
  | S.ArrowTy (t1, t2) -> occurs a t1 || occurs a t2
  | S.ProdTy (t1, t2) -> occurs a t1 || occurs a t2
  | S.ListTy t -> occurs a t


let rec solve sbst = function
  | [] ->
      sbst
  | (t1, t2) :: eqs when t1 = t2 ->
      solve sbst eqs
  | (S.ArrowTy (t1, t1'), S.ArrowTy (t2, t2')) :: eqs ->
      solve sbst ((t1, t2) :: (t1', t2') :: eqs)
  | (S.ParamTy a, t) :: eqs when not (occurs a t) ->
      let sbst' = add_subst a t sbst in
      solve sbst' (subst_equations sbst' eqs)
  | (t, S.ParamTy a) :: eqs when not (occurs a t) ->
      let sbst' = add_subst a t sbst in
      solve sbst' (subst_equations sbst' eqs)
  | (S.ProdTy (t1, t2), S.ProdTy (t1', t2')) :: eqs ->
      solve sbst ((t1, t1') :: (t2, t2') :: eqs)
  | (S.ListTy t, S.ListTy t') :: eqs ->
      solve sbst ((t, t') :: eqs)
  | (t1, t2) :: _ ->
      failwith ("Cannot solve " ^ S.string_of_ty t1 ^ " = " ^ S.string_of_ty t2)


let rec renaming sbst = function
  | S.ParamTy a ->
      if List.mem_assoc a sbst
      then sbst
      else (a, S.ParamTy (S.Param (List.length sbst))) :: sbst
  | S.IntTy | S.BoolTy -> sbst
  | S.ArrowTy (t1, t2) ->
      let sbst' = renaming sbst t1 in
      renaming sbst' t2
  | S.ProdTy (t1, t2) ->
      let sbst' = renaming sbst t1 in
      renaming sbst' t2
  | S.ListTy t -> renaming sbst t


let infer e =
  let t, eqs = infer_exp [] e in
  let sbst = solve [] eqs in
  let t' = S.subst_ty sbst t in
  let sbst' = renaming [] t' in
  let t'' = S.subst_ty sbst' t' in
  print_endline (S.string_of_exp e ^ " : " ^ S.string_of_ty t'')
