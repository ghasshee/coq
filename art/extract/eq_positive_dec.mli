
type positive =
| XI of positive
| XO of positive
| XH

type sumbool =
| Left
| Right

val eq_positive_dec : positive -> positive -> sumbool
