
type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

type sumbool =
| Left
| Right

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val merge_aux :
    ('a1 -> 'a1 -> sumbool) -> nat -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec merge_aux ale_dec bound l1 l2 =
  match bound with
  | O -> Nil
  | S n ->
    (match l1 with
     | Nil -> l2
     | Cons (a, l) ->
       (match l2 with
        | Nil -> l1
        | Cons (b, k) ->
          (match ale_dec a b with
           | Left -> Cons (a, (merge_aux ale_dec n l l2))
           | Right -> Cons (b, (merge_aux ale_dec n l1 k)))))

(** val merge :
    ('a1 -> 'a1 -> sumbool) -> 'a1 list -> 'a1 list -> 'a1 list **)

let merge ale_dec l1 l2 =
  merge_aux ale_dec (S (add (length l1) (length l2))) l1 l2
