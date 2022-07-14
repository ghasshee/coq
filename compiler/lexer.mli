
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool
 end

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat
 end

module N :
 sig
  val add : n -> n -> n

  val mul : n -> n -> n

  val to_nat : n -> nat
 end

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val n_of_digits : bool list -> n

val n_of_ascii : ascii -> n

val nat_of_ascii : ascii -> nat

type string =
| EmptyString
| String of ascii * string

val isWhite : ascii -> bool

val isAlpha : ascii -> bool

val isDigit : ascii -> bool

type chartype =
| White
| Alpha
| Digit
| Other

val classifyChar : ascii -> chartype

val list_of_string : string -> ascii list

val string_of_list : ascii list -> string

val tokenize_helper : chartype -> ascii list -> ascii list -> ascii list list

val tokenize : string -> string list
