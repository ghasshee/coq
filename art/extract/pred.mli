
type __ = Obj.t

type nat =
| O
| S of nat

val pred' : nat -> nat

val pred'_on_O : __ -> nat
