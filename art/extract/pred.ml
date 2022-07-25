
type __ = Obj.t

type nat =
| O
| S of nat

(** val pred' : nat -> nat **)

let pred' = function
| O -> assert false (* absurd case *)
| S p -> p

(** val pred'_on_O : __ -> nat **)

let pred'_on_O _ =
  pred' O
