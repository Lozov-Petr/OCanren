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
    (* (sorto xs xs') &&&
    (smallesto x s xs))] *)
    (smallesto x s xs) &&&
    (sorto xs xs'))]
and sorto x y = invoke [!!!x;!!!y] (fun [x;y] -> sorto' (!!!x) (!!!y))

(****************************)

let show_nat_list = show List.logic @@ show Nat.logic
let reify_nat_list = List.reify Nat.reify

let _ =
  (* Unfold.run (-1) Nat.reify (show Nat.logic) (fun q -> leo q (Nat.s Nat.o) Bool.truo) *)
  (* Unfold.run (-1) reify_nat_list show_nat_list (fun q -> sorto ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 50) q) *)
  Unfold.run (24) reify_nat_list show_nat_list (fun q -> sorto q (nat_list [0;1;2;4]));

(* let _ = *)
  (* 0.33 *)
  (* run_exn show_nat_list (-1) q qh (REPR (fun q -> sorto ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 20) q)); *)

  (* 12.68 *)
  (* run_exn show_nat_list (-1) q qh (REPR (fun q -> sorto ((fun k -> nat_list @@ L.init k (fun n -> k - n)) 50) q)); *)

  (* >162 [only 16 answers] *)
  (* run_exn show_nat_list (24) q qh (REPR (fun q -> sorto q (nat_list [0;1;2;4]))); *)
