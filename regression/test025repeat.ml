module L = List

open GT
open OCanren
open OCanren.Std
open Tester

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
let rec length x q23 = ((x === (nil ())) &&& (q23 === (o ()))) ||| (fresh (q25 xs q26) (x === (q25 % xs)) (q23 === (s q26)) (length xs q26))
let eq x y q10 =
  conde
    [(x === (a ())) &&& (conde [(y === (a ())) &&& (q10 === (!! true)); (y === (b ())) &&& (q10 === (!! false)); (y === (c ())) &&& (q10 === (!! false))]);
    (x === (b ())) &&& (conde [(y === (a ())) &&& (q10 === (!! false)); (y === (b ())) &&& (q10 === (!! true)); (y === (c ())) &&& (q10 === (!! false))]);
    (x === (c ())) &&& (conde [(y === (a ())) &&& (q10 === (!! false)); (y === (b ())) &&& (q10 === (!! false)); (y === (c ())) &&& (q10 === (!! true))])]
let rec check_list x q8 =
  conde
    [(x === (nil ())) &&& (q8 === (!! true));
    fresh (xs) (x === ((a ()) % xs)) (check_list xs q8);
    fresh (xs) (x === ((b ()) % xs)) (check_list xs q8);
    fresh (xs) (x === ((c ()) % xs)) (check_list xs q8)]
let rec is_repeat x q0 =
  conde
    [(x === (nil ())) &&& (q0 === (!! true));
    fresh (q2) (x === (q2 % (nil ()))) (q0 === (!! true));
    fresh (q4 y xs q6) (x === (q4 % (y % xs))) (eq q4 y q6) (conde [(q6 === (!! true)) &&& (is_repeat (y % xs) q0); (q6 === (!! false)) &&& (q0 === (!! false))])]

(***********************************************************************)

let show_a = function
| A -> "A"
| B -> "B"
| C -> "C"

let show_list x = show List.ground show_a x

let rec int2nat i = if i = 0 then o () else s (int2nat @@ i - 1)

let _ =
  run_exn show_list (-1) q qh ("test1", fun q ->
    length q (int2nat 12) &&&
    check_list q !!true &&&
    is_repeat q !!true
  )
