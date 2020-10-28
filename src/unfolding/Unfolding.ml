
module Unfold = struct

  type state = VarEnv.t * VarSubst.t

  type a = Obj.t

  type program = Unify of a * a
               | Fresh of (a -> program)
               | Invoke of def * a list
               | Conjunction of program * program
               | Disjunction of program * program
  and def      = (a list -> program)
  and call     = def * a list

  type stream  = Conj of state * call list
               | Disj of stream * stream

  (**************************************************************************)
  let unification_count  = ref 0
  let steps_calls        = ref 0
  let unfold_calls       = ref 0
  let interleaving_count = ref 0
  (**************************************************************************)

  let disj a b = Disj (a, b)
  let conj a b = Conj (a, b)

  let (>>=) x f =
    match x with
    | None -> None
    | Some x -> f x

  let rec take n l =
    if n = 0 then [] else
      match l with
      | x :: xs -> x :: take (n - 1) xs
      | []      -> []

  let unify (env, subst) a b =
    unification_count := !unification_count + 1;
    VarSubst.unify env subst a b >>= fun (_, s) -> Some (env, s)

  let fresh (env, subst) f =
    f (VarEnv.fresh env ~scope:Term.Var.non_local_scope)

  let disjCmb a b =
    match a, b with
    | None ,  b      -> b
    | a    ,  None   -> a
    | Some a, Some b -> Some (disj a b)

  (**************************************************************************)

  let prog2stream state prog =
    let rec p2s st pr = unfold_calls := !unfold_calls + 1;
      match st, pr with
      | Disj (a, b), pr                 -> disjCmb (p2s a pr) @@ p2s b pr
      | Conj (s, c), Unify (x, y)       -> unify s x y >>= fun s -> Some (conj s c)
      | Conj (s, c), Invoke (d, a)      -> Some (conj s @@ List.append c [d, a])
      | Conj (s, c), Fresh f            -> p2s st @@ fresh s f
      | st         , Conjunction (a, b) -> p2s st a >>= fun st -> p2s st b
      | st         , Disjunction (a, b) -> disjCmb (p2s st a) @@ p2s st b
    in p2s (conj state []) prog

  let unfold state (def, args) =
    prog2stream state @@ def args

  (**************************************************************************)

  let rec step stream = steps_calls := !steps_calls + 1;
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
        | Some a, ans -> interleaving_count := !interleaving_count + 1;
                         Some (disj b a), ans
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

  let run n reifier printer g =
    let getTerm (env, subst) x =
      let r = Logic.make_rr env (Obj.magic @@ VarSubst.reify env subst x) in
      r#reify reifier
    in let rec run n q stream =
      let stream, ans = step stream in
      let l           = List.length ans in
      List.iter (fun a -> Printf.printf "%s\n%!" (printer @@ getTerm a q)) @@ take n ans;
      match stream with
      | None    -> ()
      | Some st -> if n < 0 || n > l then run (n - l) q st in
    let env    = VarEnv.empty () in
    let subst  = VarSubst.empty in
    let q      = VarEnv.fresh env ~scope:Term.Var.non_local_scope in
    let stream = prog2stream (env, subst) @@ g q in
    match stream with
    | None    -> ()
    | Some st -> run n q st
end

let (!!!) = Obj.magic

module Fresh = struct
  let succ prev f = Unfold.Fresh (fun x -> prev @@ f (!!!x))
  let zero  f = f
  let one   f = succ zero f
  let two   f = succ one f
  let three f = succ two f
  let four  f = succ three f
  let five  f = succ four f
  let six   f = succ five f
end

let (===)  a b = Unfold.Unify (!!!a, !!!b)
let (|||)  a b = Unfold.Disjunction (a, b)
let (&&&)  a b = Unfold.Conjunction (a, b)
let invoke a b = Unfold.Invoke (b, List.map (!!!) a)

let rec conde = function
  | [x]     -> x
  | x :: xs -> x ||| conde xs
  | []      -> raise @@ Failure "'conde' without disjuncts"
