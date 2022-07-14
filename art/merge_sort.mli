
type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

val merge_aux :
  ('a1 -> 'a1 -> sumbool) -> nat -> 'a1 list -> 'a1 list -> 'a1 list

val merge : ('a1 -> 'a1 -> sumbool) -> 'a1 list -> 'a1 list -> 'a1 list
