module L = List

open GT
open OCanren
open OCanren.Std
open Tester

type 'a0 gpeano =
  | O
  | S of 'a0

module For_gpeano = Fmap(
  struct
    let rec fmap fa0 = function
      | O -> O
      | S a0 -> S (fa0 a0)
    type 'a0 t = 'a0 gpeano
  end)

let o ()   = inj (For_gpeano.distrib O)
let s x__0 = inj (For_gpeano.distrib (S x__0))

type a =  A | B | C
let a () = !! A
let b () = !! B
let c () = !! C

let rec length x q23 =
  ((x === (nil ())) &&& (q23 === (o ()))) |||
  (fresh (q25 xs q26)
    (x === (q25 % xs))
    (q23 === (s q26))
    (length xs q26))

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
    fresh (q4 y xs q6)
      (x === (q4 % (y % xs)))
      (eq q4 y q6)
      (conde [(q6 === (!! true)) &&& (is_repeat (y % xs) q0);
              (q6 === (!! false)) &&& (q0 === (!! false))])]

let rec is_repeat1 x q0 =
  conde
    [(x === (nil ())) &&& (q0 === (!! true));
    fresh (q2) (x === (q2 % (nil ()))) (q0 === (!! true));
    fresh (q4 y xs q6)
      (x === (q4 % (y % xs)))
      (conde [(q6 === (!! true)) &&& (eq q4 y q6) &&& (is_repeat1 (y % xs) q0);
              (q6 === (!! false)) &&& (q0 === (!! false)) &&& (eq q4 y q6)])]


(***********************************************************************)

let show_a = function
| A -> "A"
| B -> "B"
| C -> "C"

let show_list x = show List.ground show_a x

let rec int2nat i = if i = 0 then o () else s (int2nat @@ i - 1)

let _ =
  (* 199 unifications  *)
  (* 459 interleavings *)
  (* 660 mplus         *)
  (* 477 binds         *)
  (* 0.02s             *)
  run_exn show_list (-1) q qh ("repeat 2", fun q -> length q (int2nat 2) &&& check_list q !!true &&& is_repeat q !!true);

  (****************************************************************************)

  (* 1535271 unifications  *)
  (* 7666507 interleavings *)
  (* 9201780 mplus         *)
  (* 3483933 binds         *)
  (* 6.29s                 *)
  (* run_exn show_list (-1) q qh ("repeat 10", fun q -> length q (int2nat 10) &&& check_list q !!true &&& is_repeat q !!true); *)


  (*  4605823 unifications  *)
  (* 24652938 interleavings *)
  (* 29258763 mplus         *)
  (* 10451727 binds         *)
  (* 23.05s                 *)
  (* run_exn show_list (-1) q qh ("repeat 11", fun q -> length q (int2nat 11) &&& check_list q !!true &&& is_repeat q !!true); *)

  (* 13817471 unifications  *)
  (* 78918971 interleavings *)
  (* 92736444 mplus         *)
  (* 31355085 binds         *)
  (* 77.90s                 *)
  (* run_exn show_list (-1) q qh ("repeat 12", fun q -> length q (int2nat 12) &&& check_list q !!true &&& is_repeat q !!true); *)

  (****************************************************************************)
  (****************************************************************************)
  (****************************************************************************)

  (* 1564794 unifications  *)
  (* 7627143 interleavings *)
  (* 9191939 mplus         *)
  (* 3602022 binds         *)
  (* 6.39s                 *)
  (* run_exn show_list (-1) q qh ("repeat0 10", fun q -> length q (int2nat 10) &&& check_list q !!true &&& is_repeat1 q !!true); *)

  (*  4694395 unifications  *)
  (* 24534842 interleavings *)
  (* 29229239 mplus         *)
  (* 10806012 binds         *)
  (* 20.99s                 *)
  (* run_exn show_list (-1) q qh ("repeat0 11", fun q -> length q (int2nat 11) &&& check_list q !!true &&& is_repeat1 q !!true); *)

  (* 14083190 unifications  *)
  (* 78564679 interleavings *)
  (* 92647871 mplus         *)
  (* 32417958 binds         *)
  (* 74.88s                 *)
  (* run_exn show_list (-1) q qh ("repeat 12", fun q -> length q (int2nat 12) &&& check_list q !!true &&& is_repeat1 q !!true); *)



  Printf.printf "Unifications:  %10d\n" @@ Peep.unification_counter ();
  Printf.printf "Interleavings: %10d\n" @@ Peep.interleaving_counter ();
  Printf.printf "Mplus calls:   %10d\n" @@ Peep.mplus_counter ();
  Printf.printf "Bind calls:    %10d\n" @@ Peep.bind_counter ();
