module L = List

open GT
open OCanren
open OCanren.Std
open Unfolding

let rec leo' x y b = conde [
  (x === Nat.o) &&& (b === Bool.truo);
  Fresh.one (fun zz ->
    (x === Nat.s zz) &&&
    (y === Nat.o) &&&
    (b === Bool.falso));
  Fresh.two (fun x' y' ->
    (x === (Nat.s x')) &&&
    (y === (Nat.s y')) &&&
    (leo x' y' b))]
and leo x y b = invoke [!!!x;!!!y;!!!b] (fun [x;y;b] -> leo' (!!!x) (!!!y) (!!!b))

let rec gto' x y b = conde [
  Fresh.one (fun zz ->
    (x === Nat.s zz) &&&
    (y === Nat.o) &&&
    (b === Bool.truo));
  (x === Nat.o) &&& (b === Bool.falso);
  Fresh.two (fun x' y' ->
    (x === Nat.s x') &&&
    (y === Nat.s y') &&&
    (gto x' y' b))]
and gto x y b = invoke [!!!x;!!!y;!!!b] (fun [x;y;b] -> gto' (!!!x) (!!!y) (!!!b))

let minmaxo' a b min max = conde [
  (min === a) &&& (max === b) &&& (leo a b Bool.truo);
  (max === a) &&& (min === b) &&& (gto a b Bool.truo)]
let minmaxo a b min max = invoke [!!!a;!!!b;!!!min;!!!max] (fun [a;b;min;max] -> minmaxo' (!!!a) (!!!b) (!!!min) (!!!max))

let rec smallesto' l s l' = conde [
  (l === !< s) &&& (l' === nil());
  Fresh.five (fun h t s' t' max ->
    (l' === max % t') &&&
    (l === h % t) &&&
    (minmaxo h s' s max) &&&
    (smallesto t s' t'))]
and smallesto l s l' = invoke [!!!l;!!!s;!!!l'] (fun [l;s;l'] -> smallesto' (!!!l) (!!!s) (!!!l'))

let rec sorto' x y = conde [
  (x === nil()) &&& (y === nil());
  Fresh.three (fun s xs xs' ->
    (y === s % xs') &&&
    (smallesto x s xs) &&&
    (sorto xs xs'))]
and sorto x y = invoke [!!!x;!!!y] (fun [x;y] -> sorto' (!!!x) (!!!y))

let rec sorto0' x y = conde [
  (x === nil()) &&& (y === nil());
  Fresh.three (fun s xs xs' ->
    (y === s % xs') &&&
    (sorto0 xs xs') &&&
    (smallesto x s xs))]
and sorto0 x y = invoke [!!!x;!!!y] (fun [x;y] -> sorto0' (!!!x) (!!!y))

(****************************)

let show_nat_list = show List.logic @@ show Nat.logic
let reify_nat_list = List.reify Nat.reify

let _ =

  (*  4847906 unifications  *)
  (*  3265508 interleavings *)
  (*  4257135 steps         *)
  (* 15497676 unfolds       *)
  (* 18.93s                 *)
  (* Unfold.run (-1) reify_nat_list show_nat_list (fun q -> sorto ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 50) q); *)

  (*  9716811 unifications  *)
  (*  6550063 interleavings *)
  (*  8529940 steps         *)
  (* 31064006 unfolds       *)
  (* 62.67s                 *)
  (* Unfold.run (-1) reify_nat_list show_nat_list (fun q -> sorto ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 60) q); *)

  (* 13207226 unifications  *)
  (*  8903553 interleavings *)
  (* 11590655 steps         *)
  (* 42223896 unfolds       *)
  (* 82.64s                 *)
  (* Unfold.run (-1) reify_nat_list show_nat_list (fun q -> sorto ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 65) q); *)

  (***********************************************************************)
  (***********************************************************************)
  (***********************************************************************)

  (* Unifications:      351301 *)
  (* Interleavings:     521853 *)
  (* Step calls:        612934 *)
  (* Unfold calls:     1157444 *)
  (* 23.42s                    *)
  (* Unfold.run (1) reify_nat_list show_nat_list (fun q -> sorto0 ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 4) q); *)

  (***********************************************************************)
  (***********************************************************************)
  (***********************************************************************)

  (* Unifications:        1987 *)
  (* Interleavings:       2509 *)
  (* Step calls:          3002 *)
  (* Unfold calls:        6560 *)
  (* 0.02s                     *)
  (* Unfold.run (6) reify_nat_list show_nat_list (fun q -> sorto q (nat_list [0;1;2])); *)

  (* Unifications:      121653 *)
  (* Interleavings:     230661 *)
  (* Step calls:        261863 *)
  (* Unfold calls:      387269 *)
  (* 0.64s                     *)
  (* Unfold.run (24) reify_nat_list show_nat_list (fun q -> sorto q (nat_list [0;1;2;4])); *)

  (***********************************************************************)
  (***********************************************************************)
  (***********************************************************************)

  (* Unifications:      630247 *)
  (* Interleavings:    1225547 *)
  (* Step calls:       1378049 *)
  (* Unfold calls:     2026591 *)
  (* 3.24s                     *)
  Unfold.run (-1) reify_nat_list show_nat_list (fun q -> sorto0 q (nat_list [0;1;2;3;4;5;6]));

Printf.printf "Unifications:  %10d\n" !Unfold.unification_count;
Printf.printf "Interleavings: %10d\n" !Unfold.interleaving_count;
Printf.printf "Step calls:    %10d\n" !Unfold.steps_calls;
Printf.printf "Unfold calls:  %10d\n" !Unfold.unfold_calls;
