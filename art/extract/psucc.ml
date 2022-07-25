
type positive =
| XI of positive
| XO of positive
| XH

(** val psucc : positive -> positive **)

let rec psucc = function
| XI x' -> XO (psucc x')
| XO x' -> XI x'
| XH -> XO XH
