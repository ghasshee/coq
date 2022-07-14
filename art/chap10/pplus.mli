
type positive =
| XI of positive
| XO of positive
| XH

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive
 end
