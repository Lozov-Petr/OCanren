module L = List
open GT

open OCanren
open OCanren.Std
open Tester

let show_nat n    =
  let rec to_int = function
   | Nat.S n -> 1 + to_int n
   | Nat.O   -> 0 in
  show int @@ to_int n

let show_nat_list = GT.(show List.ground @@ show_nat)

let rec appendo a b ab =
  conde [
    (a === nil ()) &&& (b === ab);
    fresh (h t ab')
      (a === h % t)
      (h % ab' === ab)
      (appendo t b ab')]

let rec reverso a b =
  conde [
    (a === nil ()) &&& (b === nil ());
    fresh (h t a')
      (a === h % t)
      (reverso t a')
      (appendo a' !<h b)]


let rec reverso_bad a b =
  conde [
    (a === nil ()) &&& (b === nil ());
    fresh (h t a')
      (a === h % t)
      (appendo a' !<h b)
      (reverso_bad t a')]

let rec rnats = function
| 0 -> []
| n -> n :: rnats (n - 1)

let nats n = L.rev (rnats n)

let _ =
  (* 0.35 *)
  run_exn show_nat_list 1 q qh (REPR (fun q -> reverso (nat_list @@ nats 100) q))

  (* 4.78 *)
  (* run_exn show_nat_list 1 q qh (REPR (fun q -> reverso (nat_list @@ nats 200) q)) *)


  (* 4.45 *)
  (* run_exn show_nat_list 1 q qh (REPR (fun q -> reverso_bad (nat_list @@ nats 100) q)) *)

  (* 8.96 *)
  (* run_exn show_nat_list 1 q qh (REPR (fun q -> reverso_bad (nat_list @@ nats 120) q)) *)

  (* 20.48 *)
  (* run_exn show_nat_list 1 q qh (REPR (fun q -> reverso_bad (nat_list @@ nats 150) q)) *)
