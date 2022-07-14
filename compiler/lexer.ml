
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)
 let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n0 m =
    match n0 with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n0 m =
    match n0 with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')
 end

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p    -> XO (succ p)
  | XO p    -> XI p
  | XH      -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)
 end

module N =
 struct
  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Pos.add p q))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Pos.mul p q))

  (** val to_nat : n -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p -> Pos.to_nat p
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f a), (map f t))

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, t) -> f b (fold_right f a0 t)

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| Nil -> N0
| Cons (b, l') ->
  N.add (match b with
         | True -> Npos XH
         | False -> N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : ascii -> n **)

let n_of_ascii = function
| Ascii (a0, a1, a2, a3, a4, a5, a6, a7) ->
  n_of_digits (Cons (a0, (Cons (a1, (Cons (a2, (Cons (a3, (Cons (a4, (Cons
    (a5, (Cons (a6, (Cons (a7, Nil))))))))))))))))

(** val nat_of_ascii : ascii -> nat **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

type string =
| EmptyString
| String of ascii * string

(** val isWhite : ascii -> bool **)

let isWhite c =
  let n0 = nat_of_ascii c in
  (match match Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 O)))))))))))))))))))))))))))))))) with
         | True -> True
         | False -> Nat.eqb n0 (S (S (S (S (S (S (S (S (S O))))))))) with
   | True -> True
   | False ->
     (match Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S O)))))))))) with
      | True -> True
      | False ->
        Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))

(** val isAlpha : ascii -> bool **)

let isAlpha c =
  let n0 = nat_of_ascii c in
  (match match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S
                 O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                 n0 with
         | True ->
           Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S
             O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         | False -> False with
   | True -> True
   | False ->
     (match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              n0 with
      | True ->
        Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | False -> False))

(** val isDigit : ascii -> bool **)

let isDigit c =
  let n0 = nat_of_ascii c in
  (match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S
           O)))))))))))))))))))))))))))))))))))))))))))))))) n0 with
   | True ->
     Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   | False -> False)

type chartype =
| White
| Alpha
| Digit
| Other

(** val classifyChar : ascii -> chartype **)

let classifyChar c =
  match isWhite c with
  | True -> White
  | False ->
    (match isAlpha c with
     | True -> Alpha
     | False -> (match isDigit c with
                 | True -> Digit
                 | False -> Other))

(** val list_of_string : string -> ascii list **)

let rec list_of_string = function
| EmptyString -> Nil
| String (c, s0) -> Cons (c, (list_of_string s0))

(** val string_of_list : ascii list -> string **)

let rec string_of_list xs =
  fold_right (fun x x0 -> String (x, x0)) EmptyString xs

(** val tokenize_helper :
    chartype -> ascii list -> ascii list -> ascii list list **)

let rec tokenize_helper cls acc xs =
  let tk = match acc with
           | Nil -> Nil
           | Cons (_, _) -> Cons ((rev acc), Nil) in
  (match xs with
   | Nil -> tk
   | Cons (x, xs') ->
     (match cls with
      | White ->
        (match classifyChar x with
         | White ->
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper Alpha (Cons (x, acc)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper Alpha (Cons (x, acc))
                                       xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk
                               (tokenize_helper Alpha (Cons (x, acc)) xs')))
                     | False ->
                       app tk (tokenize_helper Alpha (Cons (x, acc)) xs'))))
            | False ->
              (match b0 with
               | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper Alpha (Cons (x, acc)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper Alpha (Cons (x, acc))
                                       xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk
                               (tokenize_helper Alpha (Cons (x, acc)) xs')))
                     | False ->
                       app tk (tokenize_helper Alpha (Cons (x, acc)) xs')))))
         | Other ->
           let tp = Other in
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper tp (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper tp (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper tp (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper tp (Cons (x, Nil)) xs'))))
            | False ->
              (match b0 with
               | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper tp (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper tp (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper tp (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper tp (Cons (x, Nil)) xs')))))
         | x0 ->
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper x0 (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper x0 (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper x0 (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper x0 (Cons (x, Nil)) xs'))))
            | False ->
              (match b0 with
               | True -> app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper x0 (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper x0 (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper x0 (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper x0 (Cons (x, Nil)) xs'))))))
      | Alpha ->
        (match classifyChar x with
         | White ->
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper Alpha (Cons (x, acc)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper Alpha (Cons (x, acc))
                                       xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk
                               (tokenize_helper Alpha (Cons (x, acc)) xs')))
                     | False ->
                       app tk (tokenize_helper Alpha (Cons (x, acc)) xs'))))
            | False ->
              (match b0 with
               | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper Alpha (Cons (x, acc)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper Alpha (Cons (x, acc))
                                       xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk
                               (tokenize_helper Alpha (Cons (x, acc)) xs')))
                     | False ->
                       app tk (tokenize_helper Alpha (Cons (x, acc)) xs')))))
         | Alpha ->
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> tokenize_helper Alpha (Cons (x, acc)) xs'
               | False ->
                 (match b1 with
                  | True -> tokenize_helper Alpha (Cons (x, acc)) xs'
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True -> tokenize_helper Alpha (Cons (x, acc)) xs'
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                tokenize_helper Alpha (Cons (x, acc)) xs'
                              | False ->
                                (match b6 with
                                 | True ->
                                   tokenize_helper Alpha (Cons (x, acc)) xs'
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             tokenize_helper Alpha (Cons (x, acc)) xs'))
                     | False -> tokenize_helper Alpha (Cons (x, acc)) xs')))
            | False ->
              (match b0 with
               | True -> tokenize_helper Alpha (Cons (x, acc)) xs'
               | False ->
                 (match b1 with
                  | True -> tokenize_helper Alpha (Cons (x, acc)) xs'
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True -> tokenize_helper Alpha (Cons (x, acc)) xs'
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                tokenize_helper Alpha (Cons (x, acc)) xs'
                              | False ->
                                (match b6 with
                                 | True ->
                                   tokenize_helper Alpha (Cons (x, acc)) xs'
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             tokenize_helper Alpha (Cons (x, acc)) xs'))
                     | False -> tokenize_helper Alpha (Cons (x, acc)) xs'))))
         | Digit ->
           let tp = Digit in
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper tp (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper tp (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper tp (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper tp (Cons (x, Nil)) xs'))))
            | False ->
              (match b0 with
               | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper tp (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper tp (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper tp (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper tp (Cons (x, Nil)) xs')))))
         | Other ->
           let tp = Other in
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper tp (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper tp (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper tp (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper tp (Cons (x, Nil)) xs'))))
            | False ->
              (match b0 with
               | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper tp (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper tp (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper tp (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper tp (Cons (x, Nil)) xs'))))))
      | Digit ->
        (match classifyChar x with
         | White ->
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper Alpha (Cons (x, acc)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper Alpha (Cons (x, acc))
                                       xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk
                               (tokenize_helper Alpha (Cons (x, acc)) xs')))
                     | False ->
                       app tk (tokenize_helper Alpha (Cons (x, acc)) xs'))))
            | False ->
              (match b0 with
               | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper Alpha (Cons (x, acc)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper Alpha (Cons (x, acc))
                                       xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk
                               (tokenize_helper Alpha (Cons (x, acc)) xs')))
                     | False ->
                       app tk (tokenize_helper Alpha (Cons (x, acc)) xs')))))
         | Alpha ->
           let tp = Alpha in
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper tp (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper tp (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper tp (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper tp (Cons (x, Nil)) xs'))))
            | False ->
              (match b0 with
               | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper tp (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper tp (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper tp (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper tp (Cons (x, Nil)) xs')))))
         | Digit ->
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> tokenize_helper Digit (Cons (x, acc)) xs'
               | False ->
                 (match b1 with
                  | True -> tokenize_helper Digit (Cons (x, acc)) xs'
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True -> tokenize_helper Digit (Cons (x, acc)) xs'
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                tokenize_helper Digit (Cons (x, acc)) xs'
                              | False ->
                                (match b6 with
                                 | True ->
                                   tokenize_helper Digit (Cons (x, acc)) xs'
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             tokenize_helper Digit (Cons (x, acc)) xs'))
                     | False -> tokenize_helper Digit (Cons (x, acc)) xs')))
            | False ->
              (match b0 with
               | True -> tokenize_helper Digit (Cons (x, acc)) xs'
               | False ->
                 (match b1 with
                  | True -> tokenize_helper Digit (Cons (x, acc)) xs'
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True -> tokenize_helper Digit (Cons (x, acc)) xs'
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                tokenize_helper Digit (Cons (x, acc)) xs'
                              | False ->
                                (match b6 with
                                 | True ->
                                   tokenize_helper Digit (Cons (x, acc)) xs'
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             tokenize_helper Digit (Cons (x, acc)) xs'))
                     | False -> tokenize_helper Digit (Cons (x, acc)) xs'))))
         | Other ->
           let tp = Other in
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper tp (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper tp (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper tp (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper tp (Cons (x, Nil)) xs'))))
            | False ->
              (match b0 with
               | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper tp (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper tp (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper tp (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper tp (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper tp (Cons (x, Nil)) xs'))))))
      | Other ->
        (match classifyChar x with
         | White ->
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper Alpha (Cons (x, acc)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper Alpha (Cons (x, acc))
                                       xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk
                               (tokenize_helper Alpha (Cons (x, acc)) xs')))
                     | False ->
                       app tk (tokenize_helper Alpha (Cons (x, acc)) xs'))))
            | False ->
              (match b0 with
               | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper Alpha (Cons (x, acc)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper Alpha (Cons (x, acc)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper Alpha (Cons (x, acc))
                                       xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk
                               (tokenize_helper Alpha (Cons (x, acc)) xs')))
                     | False ->
                       app tk (tokenize_helper Alpha (Cons (x, acc)) xs')))))
         | Other ->
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> tokenize_helper Other (Cons (x, acc)) xs'
               | False ->
                 (match b1 with
                  | True -> tokenize_helper Other (Cons (x, acc)) xs'
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True -> tokenize_helper Other (Cons (x, acc)) xs'
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                tokenize_helper Other (Cons (x, acc)) xs'
                              | False ->
                                (match b6 with
                                 | True ->
                                   tokenize_helper Other (Cons (x, acc)) xs'
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             tokenize_helper Other (Cons (x, acc)) xs'))
                     | False -> tokenize_helper Other (Cons (x, acc)) xs')))
            | False ->
              (match b0 with
               | True -> tokenize_helper Other (Cons (x, acc)) xs'
               | False ->
                 (match b1 with
                  | True -> tokenize_helper Other (Cons (x, acc)) xs'
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True -> tokenize_helper Other (Cons (x, acc)) xs'
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                tokenize_helper Other (Cons (x, acc)) xs'
                              | False ->
                                (match b6 with
                                 | True ->
                                   tokenize_helper Other (Cons (x, acc)) xs'
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             tokenize_helper Other (Cons (x, acc)) xs'))
                     | False -> tokenize_helper Other (Cons (x, acc)) xs'))))
         | x0 ->
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = x in
           (match b with
            | True ->
              (match b0 with
               | True -> app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper x0 (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper x0 (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (True, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper x0 (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper x0 (Cons (x, Nil)) xs'))))
            | False ->
              (match b0 with
               | True -> app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
               | False ->
                 (match b1 with
                  | True -> app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                  | False ->
                    (match b2 with
                     | True ->
                       (match b3 with
                        | True ->
                          app tk (tokenize_helper x0 (Cons (x, Nil)) xs')
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                app tk
                                  (tokenize_helper x0 (Cons (x, Nil)) xs')
                              | False ->
                                (match b6 with
                                 | True ->
                                   app tk
                                     (tokenize_helper x0 (Cons (x, Nil)) xs')
                                 | False ->
                                   app tk (Cons ((Cons ((Ascii (False, False,
                                     False, True, False, True, False,
                                     False)), Nil)),
                                     (tokenize_helper Other Nil xs')))))
                           | False ->
                             app tk (tokenize_helper x0 (Cons (x, Nil)) xs')))
                     | False ->
                       app tk (tokenize_helper x0 (Cons (x, Nil)) xs'))))))))

(** val tokenize : string -> string list **)

let tokenize s =
  map string_of_list (tokenize_helper White Nil (list_of_string s))
