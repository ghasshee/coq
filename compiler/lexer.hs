module Lexer where

import qualified Prelude

data Bool =
   True
 | False

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

data Nat =
   O
 | S Nat

data List a =
   Nil
 | Cons a (List a)

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

eqb :: Nat -> Nat -> Bool
eqb n m =
  case n of {
   O -> case m of {
         O -> True;
         S _ -> False};
   S n' -> case m of {
            O -> False;
            S m' -> eqb n' m'}}

leb :: Nat -> Nat -> Bool
leb n m =
  case n of {
   O -> True;
   S n' -> case m of {
            O -> False;
            S m' -> leb n' m'}}

data Positive =
   XI Positive
 | XO Positive
 | XH

data N =
   N0
 | Npos Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add0 :: Positive -> Positive -> Positive
add0 x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add0 p q);
     XO q -> XO (add0 p q);
     XH -> XI p};
   XH -> case y of {
          XI q -> XO (succ q);
          XO q -> XI q;
          XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH -> XO (succ p)};
   XH -> case y of {
          XI q -> XI (succ q);
          XO q -> XO (succ q);
          XH -> XI XH}}

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add0 y (XO (mul p y));
   XO p -> XO (mul p y);
   XH -> y}

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op p a =
  case p of {
   XI p0 -> op a (iter_op op p0 (op a a));
   XO p0 -> iter_op op p0 (op a a);
   XH -> a}

to_nat :: Positive -> Nat
to_nat x =
  iter_op add x (S O)

add1 :: N -> N -> N
add1 n m =
  case n of {
   N0 -> m;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> Npos (add0 p q)}}

mul0 :: N -> N -> N
mul0 n m =
  case n of {
   N0 -> N0;
   Npos p -> case m of {
              N0 -> N0;
              Npos q -> Npos (mul p q)}}

to_nat0 :: N -> Nat
to_nat0 a =
  case a of {
   N0 -> O;
   Npos p -> to_nat p}

rev :: (List a1) -> List a1
rev l =
  case l of {
   Nil -> Nil;
   Cons x l' -> app (rev l') (Cons x Nil)}

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (List a2) -> a1
fold_right f a0 l =
  case l of {
   Nil -> a0;
   Cons b t -> f b (fold_right f a0 t)}

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

n_of_digits :: (List Bool) -> N
n_of_digits l =
  case l of {
   Nil -> N0;
   Cons b l' ->
    add1 (case b of {
           True -> Npos XH;
           False -> N0}) (mul0 (Npos (XO XH)) (n_of_digits l'))}

n_of_ascii :: Ascii0 -> N
n_of_ascii a =
  case a of {
   Ascii a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits (Cons a0 (Cons a1 (Cons a2 (Cons a3 (Cons a4 (Cons a5 (Cons
      a6 (Cons a7 Nil))))))))}

nat_of_ascii :: Ascii0 -> Nat
nat_of_ascii a =
  to_nat0 (n_of_ascii a)

data String =
   EmptyString
 | String0 Ascii0 String

isWhite :: Ascii0 -> Bool
isWhite c =
  let {n = nat_of_ascii c} in
  orb
    (orb
      (eqb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))
      (eqb n (S (S (S (S (S (S (S (S (S O)))))))))))
    (orb (eqb n (S (S (S (S (S (S (S (S (S (S O)))))))))))
      (eqb n (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))

isAlpha :: Ascii0 -> Bool
isAlpha c =
  let {n = nat_of_ascii c} in
  orb
    (andb
      (leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) n)
      (leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (andb
      (leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        n)
      (leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

isDigit :: Ascii0 -> Bool
isDigit c =
  let {n = nat_of_ascii c} in
  andb
    (leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S O)))))))))))))))))))))))))))))))))))))))))))))))) n)
    (leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

data Chartype =
   White
 | Alpha
 | Digit
 | Other

classifyChar :: Ascii0 -> Chartype
classifyChar c =
  case isWhite c of {
   True -> White;
   False ->
    case isAlpha c of {
     True -> Alpha;
     False -> case isDigit c of {
               True -> Digit;
               False -> Other}}}

list_of_string :: String -> List Ascii0
list_of_string s =
  case s of {
   EmptyString -> Nil;
   String0 c s0 -> Cons c (list_of_string s0)}

string_of_list :: (List Ascii0) -> String
string_of_list xs =
  fold_right (\x x0 -> String0 x x0) EmptyString xs

tokenize_helper :: Chartype -> (List Ascii0) -> (List Ascii0) -> List
                   (List Ascii0)
tokenize_helper cls acc xs =
  let {tk = case acc of {
             Nil -> Nil;
             Cons _ _ -> Cons (rev acc) Nil}} in
  case xs of {
   Nil -> tk;
   Cons x xs' ->
    case cls of {
     White ->
      case classifyChar x of {
       White ->
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True ->
                        app tk (tokenize_helper Alpha (Cons x acc) xs');
                       False ->
                        case b6 of {
                         True ->
                          app tk (tokenize_helper Alpha (Cons x acc) xs');
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}};
                 False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}}};
           False ->
            case b0 of {
             True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True ->
                        app tk (tokenize_helper Alpha (Cons x acc) xs');
                       False ->
                        case b6 of {
                         True ->
                          app tk (tokenize_helper Alpha (Cons x acc) xs');
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}};
                 False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}}}}};
       Other ->
        let {tp = Other} in
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> app tk (tokenize_helper tp (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper tp (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper tp (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper tp (Cons x Nil) xs')}}};
           False ->
            case b0 of {
             True -> app tk (tokenize_helper tp (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper tp (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper tp (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper tp (Cons x Nil) xs')}}}}};
       x0 ->
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper x0 (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper x0 (Cons x Nil) xs')}}};
           False ->
            case b0 of {
             True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper x0 (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper x0 (Cons x Nil) xs')}}}}}};
     Alpha ->
      case classifyChar x of {
       White ->
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True ->
                        app tk (tokenize_helper Alpha (Cons x acc) xs');
                       False ->
                        case b6 of {
                         True ->
                          app tk (tokenize_helper Alpha (Cons x acc) xs');
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}};
                 False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}}};
           False ->
            case b0 of {
             True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True ->
                        app tk (tokenize_helper Alpha (Cons x acc) xs');
                       False ->
                        case b6 of {
                         True ->
                          app tk (tokenize_helper Alpha (Cons x acc) xs');
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}};
                 False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}}}}};
       Alpha ->
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> tokenize_helper Alpha (Cons x acc) xs';
             False ->
              case b1 of {
               True -> tokenize_helper Alpha (Cons x acc) xs';
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> tokenize_helper Alpha (Cons x acc) xs';
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> tokenize_helper Alpha (Cons x acc) xs';
                       False ->
                        case b6 of {
                         True -> tokenize_helper Alpha (Cons x acc) xs';
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> tokenize_helper Alpha (Cons x acc) xs'}};
                 False -> tokenize_helper Alpha (Cons x acc) xs'}}};
           False ->
            case b0 of {
             True -> tokenize_helper Alpha (Cons x acc) xs';
             False ->
              case b1 of {
               True -> tokenize_helper Alpha (Cons x acc) xs';
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> tokenize_helper Alpha (Cons x acc) xs';
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> tokenize_helper Alpha (Cons x acc) xs';
                       False ->
                        case b6 of {
                         True -> tokenize_helper Alpha (Cons x acc) xs';
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> tokenize_helper Alpha (Cons x acc) xs'}};
                 False -> tokenize_helper Alpha (Cons x acc) xs'}}}}};
       Digit ->
        let {tp = Digit} in
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> app tk (tokenize_helper tp (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper tp (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper tp (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper tp (Cons x Nil) xs')}}};
           False ->
            case b0 of {
             True -> app tk (tokenize_helper tp (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper tp (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper tp (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper tp (Cons x Nil) xs')}}}}};
       Other ->
        let {tp = Other} in
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> app tk (tokenize_helper tp (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper tp (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper tp (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper tp (Cons x Nil) xs')}}};
           False ->
            case b0 of {
             True -> app tk (tokenize_helper tp (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper tp (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper tp (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper tp (Cons x Nil) xs')}}}}}};
     Digit ->
      case classifyChar x of {
       White ->
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True ->
                        app tk (tokenize_helper Alpha (Cons x acc) xs');
                       False ->
                        case b6 of {
                         True ->
                          app tk (tokenize_helper Alpha (Cons x acc) xs');
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}};
                 False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}}};
           False ->
            case b0 of {
             True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True ->
                        app tk (tokenize_helper Alpha (Cons x acc) xs');
                       False ->
                        case b6 of {
                         True ->
                          app tk (tokenize_helper Alpha (Cons x acc) xs');
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}};
                 False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}}}}};
       Alpha ->
        let {tp = Alpha} in
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> app tk (tokenize_helper tp (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper tp (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper tp (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper tp (Cons x Nil) xs')}}};
           False ->
            case b0 of {
             True -> app tk (tokenize_helper tp (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper tp (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper tp (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper tp (Cons x Nil) xs')}}}}};
       Digit ->
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> tokenize_helper Digit (Cons x acc) xs';
             False ->
              case b1 of {
               True -> tokenize_helper Digit (Cons x acc) xs';
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> tokenize_helper Digit (Cons x acc) xs';
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> tokenize_helper Digit (Cons x acc) xs';
                       False ->
                        case b6 of {
                         True -> tokenize_helper Digit (Cons x acc) xs';
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> tokenize_helper Digit (Cons x acc) xs'}};
                 False -> tokenize_helper Digit (Cons x acc) xs'}}};
           False ->
            case b0 of {
             True -> tokenize_helper Digit (Cons x acc) xs';
             False ->
              case b1 of {
               True -> tokenize_helper Digit (Cons x acc) xs';
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> tokenize_helper Digit (Cons x acc) xs';
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> tokenize_helper Digit (Cons x acc) xs';
                       False ->
                        case b6 of {
                         True -> tokenize_helper Digit (Cons x acc) xs';
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> tokenize_helper Digit (Cons x acc) xs'}};
                 False -> tokenize_helper Digit (Cons x acc) xs'}}}}};
       Other ->
        let {tp = Other} in
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> app tk (tokenize_helper tp (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper tp (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper tp (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper tp (Cons x Nil) xs')}}};
           False ->
            case b0 of {
             True -> app tk (tokenize_helper tp (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper tp (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper tp (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper tp (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper tp (Cons x Nil) xs')}}}}}};
     Other ->
      case classifyChar x of {
       White ->
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True ->
                        app tk (tokenize_helper Alpha (Cons x acc) xs');
                       False ->
                        case b6 of {
                         True ->
                          app tk (tokenize_helper Alpha (Cons x acc) xs');
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}};
                 False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}}};
           False ->
            case b0 of {
             True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper Alpha (Cons x acc) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True ->
                        app tk (tokenize_helper Alpha (Cons x acc) xs');
                       False ->
                        case b6 of {
                         True ->
                          app tk (tokenize_helper Alpha (Cons x acc) xs');
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}};
                 False -> app tk (tokenize_helper Alpha (Cons x acc) xs')}}}}};
       Other ->
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> tokenize_helper Other (Cons x acc) xs';
             False ->
              case b1 of {
               True -> tokenize_helper Other (Cons x acc) xs';
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> tokenize_helper Other (Cons x acc) xs';
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> tokenize_helper Other (Cons x acc) xs';
                       False ->
                        case b6 of {
                         True -> tokenize_helper Other (Cons x acc) xs';
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> tokenize_helper Other (Cons x acc) xs'}};
                 False -> tokenize_helper Other (Cons x acc) xs'}}};
           False ->
            case b0 of {
             True -> tokenize_helper Other (Cons x acc) xs';
             False ->
              case b1 of {
               True -> tokenize_helper Other (Cons x acc) xs';
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> tokenize_helper Other (Cons x acc) xs';
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> tokenize_helper Other (Cons x acc) xs';
                       False ->
                        case b6 of {
                         True -> tokenize_helper Other (Cons x acc) xs';
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> tokenize_helper Other (Cons x acc) xs'}};
                 False -> tokenize_helper Other (Cons x acc) xs'}}}}};
       x0 ->
        case x of {
         Ascii b b0 b1 b2 b3 b4 b5 b6 ->
          case b of {
           True ->
            case b0 of {
             True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii True False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper x0 (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper x0 (Cons x Nil) xs')}}};
           False ->
            case b0 of {
             True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
             False ->
              case b1 of {
               True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
               False ->
                case b2 of {
                 True ->
                  case b3 of {
                   True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
                   False ->
                    case b4 of {
                     True ->
                      case b5 of {
                       True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
                       False ->
                        case b6 of {
                         True -> app tk (tokenize_helper x0 (Cons x Nil) xs');
                         False ->
                          app tk (Cons (Cons (Ascii False False False True
                            False True False False) Nil)
                            (tokenize_helper Other Nil xs'))}};
                     False -> app tk (tokenize_helper x0 (Cons x Nil) xs')}};
                 False -> app tk (tokenize_helper x0 (Cons x Nil) xs')}}}}}}}}

tokenize :: String -> List String
tokenize s =
  map string_of_list (tokenize_helper White Nil (list_of_string s))

