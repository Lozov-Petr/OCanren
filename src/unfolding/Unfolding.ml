
module Unfolding = struct

  type state = VarEnv.t * Term.Var.scope * VarSubst.t


  type 'a program = Unify of 'a * 'a
                  | Fresh of ('a -> 'a program)
                  | Invoke of 'a def * 'a list
                  | Conjunction of 'a program * 'a program
                  | Disjunction of 'a program * 'a program
  and 'a def      = ('a list -> 'a program)
  and 'a call     = 'a def * 'a list

  type 'a stream = Conj of state * 'a call list
                 | Disj of 'a stream * 'a stream

  (**************************************************************************)

  let disj a b = Disj (a, b)
  let conj a b = Conj (a, b)

  let (>>=) x f =
    match x with
    | None -> None
    | Some x -> f x

  let unify (env, scope, subst) a b =
    VarSubst.unify env subst a b >>= fun (_, s) -> Some (env, scope, s)

  let fresh (env, scope, subst) f =
    f (VarEnv.fresh ~scope env)

  let disjCmb a b =
    match a, b with
    | None , b        -> b
    | a    , None     -> a
    | Some a, Some b -> Some (disj a b)

  (**************************************************************************)

  let unfold state (def, args) =
    let rec p2s st pr =
      match st, pr with
      | Disj (a, b), pr                 -> disjCmb (p2s a pr) @@ p2s b pr
      | Conj (s, c), Unify (x, y)       -> unify s x y >>= fun s -> Some (conj s c)
      | Conj (s, c), Invoke (d, a)      -> Some (conj s @@ List.append c [d, a])
      | Conj (s, c), Fresh f            -> p2s st @@ fresh s f
      | st         , Conjunction (a, b) -> p2s st a >>= fun st -> p2s st b
      | st         , Disjunction (a, b) -> disjCmb (p2s st a) @@ p2s st b
    in p2s (conj state []) @@ def args

  (**************************************************************************)

  let rec step stream =
    let rec splitAnswers stream =
      match stream with
      | Disj (a, b)  ->
        let s1, a1 = splitAnswers a in
        let s2, a2 = splitAnswers b in
        disjCmb s1 s2, a1 @ a2
      | Conj (a, []) -> None, [a]
      | Conj _       -> Some stream, []
    in let rec attachConjs cs = function
      | Disj (a, b) -> disj (attachConjs cs a) @@ attachConjs cs b
      | Conj (s, c) -> conj s @@ c @ cs
    in match stream with
    | Disj (a, b) ->
      begin match step a with
        | None, ans   -> Some b, ans
        | Some a, ans -> Some (disj b a), ans
      end
    | Conj (s, (c::cs)) ->
      begin match unfold s c with
      | None    -> None, []
      | Some st ->
        match cs with
        | [] -> splitAnswers st
        | _  -> Some (attachConjs cs st), []
      end
    | _ -> raise @@ Failure "Unexpected stream configuration"

end
