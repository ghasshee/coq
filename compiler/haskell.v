Require Import Extraction . 

Extraction Language Haskell .


Require Import Coq.Strings.String . 
Require Import Coq.Lists.List . 
Require Import Coq.Arith.Arith .
Require Import Coq.Arith.EqNat . 
Require Import lexer. 

Extraction "lexer.hs" tokenize.

(*
Inductive optionE (X:Type) : Type := 
    | SomeE : X         -> optionE X 
    | NoneE : string    -> optionE X . 

Implicit Arguments SomeE [[X]].



Notation "'Do' ( x , y ) <=== e1 ; e2" := 
    (match e1
*)
