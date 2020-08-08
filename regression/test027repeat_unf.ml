module L = List

open GT
open OCanren
open OCanren.Std
open Unfolding


type 'a0 gpeano =
  | O
  | S of 'a0
module For_gpeano = (Fmap)(struct let rec fmap fa0 = function | O -> O | S a0 -> S (fa0 a0)
                                  type 'a0 t = 'a0 gpeano end)
let rec o () = inj (For_gpeano.distrib O)
and s x__0 = inj (For_gpeano.distrib (S x__0))
type a =
  | A
  | B
  | C
let a () = !! A
let b () = !! B
let c () = !! C


let rec length' x q23 = conde [
  (x === (nil ())) &&& (q23 === (o ()));
  Fresh.three (fun q25 xs q26 ->
    (x === (q25 % xs)) &&&
    (q23 === (s q26)) &&&
    (length xs q26))]
and length x q23 = invoke [!!!x; !!!q23] (fun [x; q23] -> length' (!!!x) (!!!q23))


let eq' x y q10 =
  conde
    [(x === (a ())) &&& (conde [(y === (a ())) &&& (q10 === (!! true)); (y === (b ())) &&& (q10 === (!! false)); (y === (c ())) &&& (q10 === (!! false))]);
    (x === (b ())) &&& (conde [(y === (a ())) &&& (q10 === (!! false)); (y === (b ())) &&& (q10 === (!! true)); (y === (c ())) &&& (q10 === (!! false))]);
    (x === (c ())) &&& (conde [(y === (a ())) &&& (q10 === (!! false)); (y === (b ())) &&& (q10 === (!! false)); (y === (c ())) &&& (q10 === (!! true))])]
let eq x y q10 = invoke [!!!x; !!!y; !!!q10] (fun [x;y;q10] -> eq' (!!!x) (!!!y) (!!!q10))


let rec check_list' x q8 =
  conde
    [(x === (nil ())) &&& (q8 === (!! true));
    Fresh.one (fun xs ->
      (x === ((a ()) % xs)) &&&
      (check_list xs q8));
    Fresh.one (fun xs ->
      (x === ((b ()) % xs)) &&&
      (check_list xs q8));
    Fresh.one (fun xs ->
      (x === ((c ()) % xs)) &&&
      (check_list xs q8))]
and check_list x q8 = invoke [!!!x; !!!q8] (fun [x;q8] -> check_list' (!!!x) (!!!q8))

let rec is_repeat' x q0 =
  conde
    [(x === (nil ())) &&& (q0 === (!! true));
    Fresh.one (fun q2 ->
      (x === (q2 % (nil ()))) &&&
      (q0 === (!! true)));
    Fresh.four (fun q4 y xs q6 ->
      (x === (q4 % (y % xs))) &&&
      (eq q4 y q6) &&&
      (conde [(q6 === (!! true)) &&& (is_repeat (y % xs) q0); (q6 === (!! false)) &&& (q0 === (!! false))]))]
and is_repeat x q0 = invoke [!!!x; !!!q0] (fun [x; q0] -> is_repeat' (!!!x) (!!!q0))

(***********************************************************************)

let show_a = function
| A -> "A"
| B -> "B"
| C -> "C"

let reify_a : VarEnv.t -> (a, a logic) injected -> a logic = OCanren.reify

let show_list = show List.logic @@ show logic show_a
let reify_list = List.reify reify_a

let rec int2nat i = if i = 0 then o () else s (int2nat @@ i - 1)

let _ =
  (* 202 unifications *)
  Unfold.run (-1) reify_list show_list (fun q -> length q (int2nat 2) &&& is_repeat q !!true &&& check_list q !!true);

  (* 1564794 unifications *)
  (* Unfold.run (-1) reify_list show_list (fun q -> length q (int2nat 10) &&& check_list q !!true &&& is_repeat q !!true); *)
  (* 3.53s *)

  (* 4694395 unifications *)
  (* 11.61s *)
  (* Unfold.run (-1) reify_list show_list (fun q -> length q (int2nat 11) &&& check_list q !!true &&& is_repeat q !!true); *)

  Printf.printf "\nUnifications: %d\n" !Unfold.unification_count
