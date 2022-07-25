
type __ = Obj.t

type nat =
| O
| S of nat

val pred : nat -> nat

val acc_iter : ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

val well_founded_induction : ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

val div2 : nat -> nat

val log2_aux_F : nat -> (nat -> __ -> nat) -> nat

val log2_aux : nat -> nat

val log2 : nat -> nat
