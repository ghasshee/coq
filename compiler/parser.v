Require Import Coq.Strings.String . 
Require Import Coq.Lists.List . 
Require Import Coq.Arith.Arith .
Require Import Coq.Arith.EqNat . 
Require Import lexer. 


Inductive optionE (X:Type) : Type := 
    | SomeE : X         -> optionE X 
    | NoneE : string    -> optionE X . 

Implicit Arguments SomeE [[X]].
Implicit Arguments NoneE [[X]].



Notation "'Do' ( x , y ) <== e1 ; e2" :=  
    (match e1 with 
    | SomeE (x,y)   => e2
    | NoneE err     => NoneE err 
    end) 
(right associativity, at level 60) . 

