module L = List

open GT
open OCanren
open OCanren.Std
open Tester

let rec leo x y b = conde [
  (x === Nat.o) &&& (b === Bool.truo);
  fresh (zz)
    (x === Nat.s zz)
    (y === Nat.o)
    (b === Bool.falso);
  fresh (x' y')
    (x === (Nat.s x'))
    (y === (Nat.s y'))
    (leo x' y' b)]

let rec gto x y b = conde [
  fresh (zz)
    (x === Nat.s zz)
    (y === Nat.o)
    (b === Bool.truo);
  (x === Nat.o) &&& (b === Bool.falso);
  fresh (x' y')
    (x === Nat.s x')
    (y === Nat.s y')
    (gto x' y' b)]

let minmaxo a b min max = conde [
  (min === a) &&& (max === b) &&& (leo a b Bool.truo);
  (max === a) &&& (min === b) &&& (gto a b Bool.truo)]

let rec smallesto l s l' = conde
  [ (l === !< s) &&& (l' === nil())
  ; fresh (h t s' t' max)
      (l' === max % t')
      (l === h % t)
      (minmaxo h s' s max)
      (smallesto t s' t')
  ]

let rec sorto x y = conde [
  (x === nil()) &&& (y === nil());
  fresh (s xs xs')
    (y === s % xs')
    (smallesto x s xs)
    (sorto xs xs')]

let rec sorto' x y = conde [
  (x === nil()) &&& (y === nil());
  fresh (s xs xs')
    (y === s % xs')
    (sorto' xs xs')
    (smallesto x s xs)]

(****************************)

let show_nat n =
  let rec to_int = function
   | Nat.S n -> 1 + to_int n
   | Nat.O   -> 0 in
  show int @@ to_int n

let show_nat_list = GT.(show List.ground @@ show_nat)

let _ =
  (* 163841 unifications  *)
  (* 439469 interleavings *)
  (* 603310 mplus         *)
  (* 540113 binds         *)
  (* 0.40                 *)
  run_exn show_nat_list (-1) q qh ("sort 20", fun q -> sorto ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 20) q);

  (*  4847906 unifications  *)
  (* 13389643 interleavings *)
  (* 18237549 mplus         *)
  (* 16222318 binds         *)
  (* 26.08s                 *)
  (* run_exn show_nat_list (-1) q qh ("sort 50", fun q -> sorto ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 50) q); *)


  (*  9716811 unifications  *)
  (* 26912169 interleavings *)
  (* 36628980 mplus         *)
  (* 32587603 binds         *)
  (* 74.41s                 *)
  (* run_exn show_nat_list (-1) q qh ("sort 60", fun q -> sorto ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 60) q); *)

  (* 13207226 unifications  *)
  (* 36617037 interleavings *)
  (* 49824263 mplus         *)
  (* 44333333 binds         *)
  (* 93.14s                 *)
  (* run_exn show_nat_list (-1) q qh ("sort 65", fun q -> sorto ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 65) q); *)


  (***********************************************************************)
  (***********************************************************************)
  (***********************************************************************)

  (* Unifications:       58419 *)
  (* Interleavings:     147885 *)
  (* Mplus calls:       206221 *)
  (* Bind calls:        169213 *)
  (* 1.26s                     *)
  (* run_exn show_nat_list (1) q qh ("sort' 4", fun q -> sorto' ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 4) q); *)

  (* > 82.52s *)
  (* run_exn show_nat_list (1) q qh ("sort' 4", fun q -> sorto' ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 5) q); *)

  (***********************************************************************)
  (***********************************************************************)
  (***********************************************************************)

  (* Unifications:       23244 *)
  (* Interleavings:      63297 *)
  (* Mplus calls:        86418 *)
  (* Bind calls:         68022 *)
  (* 0.10s                     *)
  (* run_exn show_nat_list (6) q qh (REPR (fun q -> sorto q (nat_list [0;1;2]))); *)

  (* >162 [only 16 answers] *)
  (* run_exn show_nat_list (24) q qh (REPR (fun q -> sorto q (nat_list [0;1;2;3]))); *)

  (***********************************************************************)
  (***********************************************************************)
  (***********************************************************************)

  (* Unifications:      630247 *)
  (* Interleavings:    2414886 *)
  (* Mplus calls:      3050172 *)
  (* Bind calls:       1752605 *)
  (* 3.92s *)
  (* run_exn show_nat_list (-1) q qh (REPR (fun q -> sorto' q (nat_list [0;1;2;3;4;5;6]))); *)

  Printf.printf "Unifications:  %10d\n" @@ Peep.unification_counter ();
  Printf.printf "Interleavings: %10d\n" @@ Peep.interleaving_counter ();
  Printf.printf "Mplus calls:   %10d\n" @@ Peep.mplus_counter ();
  Printf.printf "Bind calls:    %10d\n" @@ Peep.bind_counter ();
