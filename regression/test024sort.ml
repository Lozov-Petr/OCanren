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
    (* (sorto xs xs')
    (smallesto x s xs)] *)
    (smallesto x s xs)
    (sorto xs xs')]

(****************************)

let show_nat n =
  let rec to_int = function
   | Nat.S n -> 1 + to_int n
   | Nat.O   -> 0 in
  show int @@ to_int n

let show_nat_list = GT.(show List.ground @@ show_nat)

let _ =
  (* 0.33 *)
  (* run_exn show_nat_list (-1) q qh (REPR (fun q -> sorto ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 20) q)); *)

  (* 12.68 *)
  (* run_exn show_nat_list (-1) q qh (REPR (fun q -> sorto ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 50) q)); *)

  (* 23244 unifications *)
  (* run_exn show_nat_list (6) q qh (REPR (fun q -> sorto q (nat_list [0;1;2]))); *)

  (* >162 [only 16 answers] *)
  run_exn show_nat_list (6) q qh (REPR (fun q -> sorto q (nat_list [0;1;2;3])));
  Printf.printf "\n\nUnifications: %d\n" @@ Peep.unification_counter ()
