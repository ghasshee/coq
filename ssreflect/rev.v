From mathcomp Require Import all_ssreflect.


Set Implicit Arguments. 
Unset Strict Implicit. 

Section Rev.

    Variable T : Type.

    Definition rcons' s (a : T ) := s ++ [:: a]. 

    Fixpoint reverse (s : seq T) : seq T := match s with
        | nil       => nil
        | h :: t    => rcons' (reverse t) h 
    end.

    Fixpoint catrev (s1 s2 : seq T) : seq T :=  match s1 with 
        | [::]      => nil
        | x :: s1   => catrev s1 ( x :: s2 ) 
    end.

    Definition rev (s: seq T)  : seq T := catrev s [::] .

    Lemma cat_cons ( x: T ) ( s1 s2 : seq T ) : 
        (x :: s1) ++ s2 = x :: (s1 ++ s2) .
    Proof. 
        reflexivity. 
    Qed. 


    Lemma l_rev_cat_r (s s1 s2 : seq T) : 
        catrev s (s1 ++ s2) 


