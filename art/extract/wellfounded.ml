
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type nat =
| O
| S of nat

(** val pred : nat -> nat **)

let pred n = match n with
| O -> n
| S u -> u

(** val acc_iter : ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let rec acc_iter f x =
  f x (fun y _ -> acc_iter f y)

(** val well_founded_induction :
    ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let well_founded_induction =
  acc_iter

(** val div2 : nat -> nat **)

let rec div2 = function
| O -> O
| S n0 -> (match n0 with
           | O -> O
           | S p -> S (div2 p))

(** val log2_aux_F : nat -> (nat -> __ -> nat) -> nat **)

let log2_aux_F x x0 =
  match x with
  | O -> O
  | S p -> S (x0 (div2 (S p)) __)

(** val log2_aux : nat -> nat **)

let log2_aux =
  well_founded_induction log2_aux_F

(** val log2 : nat -> nat **)

let log2 x =
  log2_aux (pred x)
