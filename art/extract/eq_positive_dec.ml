
type positive =
| XI of positive
| XO of positive
| XH

type sumbool =
| Left
| Right

(** val eq_positive_dec : positive -> positive -> sumbool **)

let rec eq_positive_dec n m =
  match n with
  | XI p -> (match m with
             | XI q -> eq_positive_dec p q
             | _ -> Right)
  | XO p -> (match m with
             | XO q -> eq_positive_dec p q
             | _ -> Right)
  | XH -> (match m with
           | XH -> Left
           | _ -> Right)
