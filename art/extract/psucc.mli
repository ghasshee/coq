
type positive =
| XI of positive
| XO of positive
| XH

val psucc : positive -> positive
