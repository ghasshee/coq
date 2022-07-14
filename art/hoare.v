Require Import ZArith List. 

Section little_semantics. 
    Variables Var aExp bExp : Set . 

    Inductive inst : Set := 
        | Skip      :                   inst
        | Assign    : Var   -> aExp ->  inst
        | Seq       : inst  -> inst ->  inst 
        | WhileDo   : bExp  -> inst ->  inst. 

    Variables 
        (state  : Set)
        (update : state -> Var -> Z -> option state)
        (evalA  : state -> aExp -> option Z)
        (evalB  : state -> bExp -> option bool). 

    Inductive exec : state -> inst -> state -> Prop := 
        | execSkip      : forall s : state, exec s Skip s
        | execAssign    : forall s s1 v n a, 
                evalA s a = Some n  ->  update s v n = Some s1  ->  exec s(Assign v a)s1
        | execSeq       : forall s s1 s2 i1 i2, 
                exec s i1 s1    ->  exec s1 i2 s2   ->  exec s (Seq i1 i2) s2 
        | execWhileTrue : forall s s1 s2 i e, 
                evalB s e = Some true   ->  exec s i s1     ->  exec s1(WhileDo e i)s2  -> 
                exec s(WhileDo e i)s2.


Theorem HoareWhileRule : forall (P:state->Prop) b i s s',
    (forall s1 s2,  P s1  ->  evalB s1 b = Some true    ->  exec s1 i s2    ->  P s2  ) ->
    P s -> exec s (WhileDo b i) s' -> P s' /\ evalB s' b = Some false . 
Proof. 
    intros P b i s s' H. 
    cut (forall i', exec s i' s' -> i' = WhileDo b i -> P s -> P s' /\ evalB s' b = Some false);
    eauto. 
    intros i' Hexec ; elim Hexec; try (intros; discriminate).  
    intros. 
    injection H5; intros. subst i0 e.  
    apply H4; trivial. 
    eapply H. 
    eauto. 
    assumption. 
    assumption. 
Qed. 


(* ex 8.26 *)
Theorem while_skip_loop : forall s s' b, exec s ( WhileDo b Skip ) s' -> evalB s b = Some true -> False. 
Proof. 
    intros s s' b H.  
    cut (forall i, exec s i s' -> i=WhileDo b Skip -> evalB s b = Some true -> False); eauto.  
    intros i Hexec; elim Hexec; try (intros; discriminate).  

    intros. 
    injection H5; intros. 
    subst i0 e. 

    inversion H1. 
    subst s1 s3. 
    apply H4; trivial. 

Qed. 



(* ex. 15.20 *)

Require Import Zwf ZArith. 
Require Import Wellfounded Inverse_Image . 
Open Scope Z_scope. 

Definition extract_option {A} (x:option A) default : A :=
  match x with 
  | None    => default
  | Some v  => v        end. 

Print Zwf. 

Inductive forLoops : inst -> Prop := 
  | aForLoop : forall (b:bExp) (i:inst) (x:aExp),
      (forall s s':state, evalB s b = Some true -> exec s i s' -> 
          Zwf 0 (extract_option (evalA s' x) 0)(extract_option (evalA s x) 0) ) -> 
      forLoops i -> forLoops (WhileDo b i) 
  | assignFor : forall v a , forLoops (Assign v a)
  | skipFor   : forLoops Skip
  | seqFor    : forall i1 i2, forLoops i1 -> forLoops i2 -> forLoops (Seq i1 i2). 


Goal forall s i, forLoops i -> 
  {s' | exec s i s'} + {forall s', ~ exec s i s'}. 
(* write the proof here *) 
Admitted. 

End little_semantics. 



