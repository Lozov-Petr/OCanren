open GT
open OCanren
open OCanren.Std
type 'a0 gpeano =
  | O
  | S of 'a0
module For_gpeano = (Fmap)(struct let rec fmap fa0 = function | O -> O | S a0 -> S (fa0 a0)
                                  type 'a0 t = 'a0 gpeano end)
let rec o () = inj (For_gpeano.distrib O)
and s x__0 = inj (For_gpeano.distrib (S x__0))
type person =
  | A
  | B
  | C
  | D
let a () = !! A
let b () = !! B
let c () = !! C
let d () = !! D
type 'a0 gstep =
  | One of 'a0
  | Two of 'a0 * 'a0
module For_gstep = (Fmap)(struct let rec fmap fa0 = function | One a0 -> One (fa0 a0) | Two (a0_0, a0_1) -> Two ((fa0 a0_0), (fa0 a0_1))
                                 type 'a0 t = 'a0 gstep end)
let rec one x__0 = inj (For_gstep.distrib (One x__0))
and two x__0 x__1 = inj (For_gstep.distrib (Two (x__0, x__1)))
type 'a0 gstate =
  | St of 'a0 * 'a0 * 'a0 * 'a0 * 'a0
module For_gstate =
  (Fmap)(struct let rec fmap fa0 = function | St (a0_0, a0_1, a0_2, a0_3, a0_4) -> St ((fa0 a0_0), (fa0 a0_1), (fa0 a0_2), (fa0 a0_3), (fa0 a0_4))
                type 'a0 t = 'a0 gstate end)
let rec st x__0 x__1 x__2 x__3 x__4 = inj (For_gstate.distrib (St (x__0, x__1, x__2, x__3, x__4)))
let eqBool x y q133 =
  ((x === (!! true)) &&& (y === q133)) ||| ((x === (!! false)) &&& (conde [(y === (!! true)) &&& (q133 === (!! false)); (y === (!! false)) &&& (q133 === (!! true))]))
let eqState x y q107 =
  fresh (a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 q109 q110 q115 q116 q121 q122 q127 q128) (
    x === (st a1 a2 a3 a4 a5)) (y === (st b1 b2 b3 b4 b5)) (eqBool a1 b2 q109) (
    eqBool a2 b2 q115) (eqBool a3 b3 q121) (eqBool a4 b4 q127) (eqBool a5 b5 q128)
    (conde [(q127 === (!! false)) &&& (q122 === (!! false)); (q127 === (!! true)) &&& (q122 === q128)])
    (conde [(q121 === (!! false)) &&& (q116 === (!! false)); (q121 === (!! true)) &&& (q116 === q122)])
    (conde [(q115 === (!! false)) &&& (q110 === (!! false)); (q115 === (!! true)) &&& (q110 === q116)])
    (conde [(q109 === (!! false)) &&& (q107 === (!! false)); (q109 === (!! true)) &&& (q107 === q110)])
let rec greater a0 b0 q103 =
  ((a0 === (o ())) &&& (q103 === (!! false))) ||| (fresh (x) (a0 === (s x)) (((b0 === (o ())) &&& (q103 === (!! true))) ||| (fresh (y) (b0 === (s y)) (greater x y q103))))
let grForPerson x y q86 =
  conde
    [(x === (a ())) &&&
       (conde [(y === (a ())) &&& (q86 === (!! false)); (y === (b ())) &&& (q86 === (!! true)); (y === (c ())) &&& (q86 === (!! true)); (y === (d ())) &&& (q86 === (!! true))]);
    (x === (b ())) &&&
      (conde [(y === (a ())) &&& (q86 === (!! false)); (y === (b ())) &&& (q86 === (!! false)); (y === (c ())) &&& (q86 === (!! false)); (y === (d ())) &&& (q86 === (!! true))]);
    (x === (c ())) &&&
      (conde [(y === (a ())) &&& (q86 === (!! false)); (y === (b ())) &&& (q86 === (!! false)); (y === (c ())) &&& (q86 === (!! false)); (y === (d ())) &&& (q86 === (!! true))]);
    (x === (d ())) &&& (q86 === (!! false))]
let max a0 b0 q82 = fresh (q83) (greater a0 b0 q83) (conde [(q83 === (!! true)) &&& (a0 === q82); (q83 === (!! false)) &&& (b0 === q82)])
let rec add a0 b0 q80 = ((a0 === (o ())) &&& (b0 === q80)) ||| (fresh (x) (a0 === (s x)) (add x (s b0) q80))
let checkPerson state person q78 =
  fresh (l a0 b0 c0 d0) (state === (st l a0 b0 c0 d0))
    (conde
       [(person === (a ())) &&& (eqBool a0 l q78); (person === (b ())) &&& (eqBool b0 l q78); (person === (c ())) &&& (eqBool c0 l q78); (person === (d ())) &&& (eqBool d0 l q78)])
let checkStep state step q65 =
  (fresh (p) (step === (one p)) (checkPerson state p q65)) |||
    (fresh (p q q66 q67 q72 q73) (step === (two p q)) (checkPerson state p q66) (
       checkPerson state q q72) (grForPerson p q q73) (conde [(q72 === (!! false)) &&& (q67 === (!! false)); (q72 === (!! true)) &&& (q67 === q73)])
       (conde [(q66 === (!! false)) &&& (q65 === (!! false)); (q66 === (!! true)) &&& (q65 === q67)]))
let moveLight state q60 =
  fresh (l a0 b0 c0 d0 q61) (state === (st l a0 b0 c0 d0)) (q60 === (st q61 a0 b0 c0 d0))
    (conde [(l === (!! true)) &&& (q61 === (!! false)); (l === (!! false)) &&& (q61 === (!! true))])
let movePerson state person q42 =
  fresh (l a0 b0 c0 d0) (state === (st l a0 b0 c0 d0))
    (conde
       [fresh (q44) (person === (a ())) (q42 === (st l q44 b0 c0 d0)) (conde [(a0 === (!! true)) &&& (q44 === (!! false)); (a0 === (!! false)) &&& (q44 === (!! true))]);
       fresh (q48) (person === (b ())) (q42 === (st l a0 q48 c0 d0)) (conde [(b0 === (!! true)) &&& (q48 === (!! false)); (b0 === (!! false)) &&& (q48 === (!! true))]);
       fresh (q52) (person === (c ())) (q42 === (st l a0 b0 q52 d0)) (conde [(c0 === (!! true)) &&& (q52 === (!! false)); (c0 === (!! false)) &&& (q52 === (!! true))]);
       fresh (q56) (person === (d ())) (q42 === (st l a0 b0 c0 q56)) (conde [(d0 === (!! true)) &&& (q56 === (!! false)); (d0 === (!! false)) &&& (q56 === (!! true))])])
let step state step q35 =
  (fresh (p q36) (step === (one p)) (movePerson state p q36) (moveLight q36 q35)) |||
    (fresh (p q q38 q40) (step === (two p q)) (movePerson state p q40) (movePerson q40 q q38) (moveLight q38 q35))
let times p q30 =
  conde
    [(p === (a ())) &&& (q30 === (s (o ())));
    (p === (b ())) &&& (q30 === (s (s (o ()))));
    (p === (c ())) &&& (q30 === (s (s (s (s (s (o ())))))));
    (p === (d ())) &&& (q30 === (s (s (s (s (s (s (s (s (s (s (o ()))))))))))))]
let getTime state q26 = (fresh (p) (state === (one p)) (times p q26)) ||| (fresh (p q q27 q28) (state === (two p q)) (times p q27) (times q q28) (max q27 q28 q26))
let getAnswer answer q25 =
  let start q0 = q0 === (st (!! true) (!! true) (!! true) (!! true) (!! true)) in
  let finish q1 = q1 === (st (!! false) (!! false) (!! false) (!! false) (!! false)) in
  let rec getAnswer answer state q2 =
    (fresh (x xs q4) (answer === (x % xs)) (checkStep state x q4)
       (conde
          [fresh (q6 q12) (q4 === (!! true)) (step state x q12) (getAnswer xs q12 q6)
             (((q6 === (none ())) &&& (q2 === (none ()))) ||| (fresh (t1 q8 q10) (q6 === (some t1)) (q2 === (some q8)) (getTime x q10) (add q10 t1 q8)));
          (q4 === (!! false)) &&& (q2 === (none ()))]))
      |||
      (fresh (q16 q19) (answer === (nil ())) (finish q19) (eqState state q19 q16)
         (conde [(q16 === (!! true)) &&& (q2 === (some (o ()))); (q16 === (!! false)) &&& (q2 === (none ()))])) in
  fresh (q21) (start q21) (getAnswer answer q21 q25)

(*************************************************)
(*************************************************)
(*************************************************)

open Tester

let show_person = function
| A -> "A"
| B -> "B"
| C -> "C"
| D -> "D"

let show_step f = function
| One x     -> f x
| Two (x,y) -> Printf.sprintf "(%s, %s)" (f x) (f y)

let myshow x = show List.ground (show_step show_person) x

(*************************************************)

let rec int2nat i = if i = 0 then o () else s @@ int2nat @@ i - 1

let _ =
  (* 91 *)
  run_exn myshow (1) q qh ("answers", fun q -> getAnswer q (int2nat 17 |> some))
