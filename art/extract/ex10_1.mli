
type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

type 'a option =
| Some of 'a
| None

val nth' : 'a1 list -> nat -> 'a1 option
