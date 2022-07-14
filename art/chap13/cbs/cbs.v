

(* Notation "∀ a , P" := (forall a, P ) (at level 100, right associativity). *)

(*
Inductive nat : Set := O : nat | S : nat -> nat . 
*)
(*
CoInductive Stream A : Type := 
    | cons : A -> Stream A -> Stream A . 

Definition hd {A} (x:Stream A) : A := 
    match x with 
    | cons a s => a     end. 

Definition tl {A}(x:Stream A) : Stream A := 
    match x with 
    | cons a s => s     end. 

CoFixpoint zeros  := cons O zeros . 
CoFixpoint from n := cons n (from (S n)). 
CoFixpoint alter  := cons true (cons false alter). 

Compute (hd (tl (tl (tl (from 3))))). 

CoFixpoint append {A} (s1 s2:Stream A) : Stream A := 
    cons (hd s1) (append (tl s1) s2) . 

Notation "A ++ B" := (append A B). 

CoInductive Eq   { A } (s1 s2: Stream A) : Prop := 
    eqst : hd s1 = hd s2 -> Eq (tl s1)(tl s2) -> Eq s1 s2. 

CoFixpoint proof { A } (s1 s2:Stream A) : Eq s1 (s1 ++ s2) := 
    eqst s1 (s1 ++ s2) (eq_refl (hd s1)) (proof (tl s1) s2) . 

*)


(* CBS : Calculus of Broadcasting Systems *) 


(* broadcast : one process speaks, many can hear at the same time *) 

Require Import Streams. 

Section Process. 
    Variable Channel : Set . 
    Variable A : Channel -> Set . 
    
    CoInductive Process : Set :=
      | TALK      : forall c1,  A c1 (* sending val *) -> 
                    Process (* listener process *) -> 
                    forall c2, (A c2 -> Process) (* send process : after sender sent a value x, they does f(x)*)-> 
                    Process 
      | LISTEN    : forall c, (A c -> Process) (* if recieved a value x:A, then do f(x) *) -> 
                    Process 
      | PAR       : Process -> Process -> Process
      | NIL       : Process . 



    (* action is a state transition function between processes *)
    (* Process --action--> Process'' *)  
    Inductive Signal (c:Channel) : Set := 
        | Noise     : Signal c
        | Clear     : A c -> Signal c. 

    Inductive Action (c:Channel) : Set := 
        | Transmit  : Signal c -> Action c
        | Receive   : A c      -> Action c. 

    (* Coercion Transmit : Signal>-> Action *)

    Notation "! a" := (Transmit _ a) (at level 0). 
    Notation "? a" := (Receive  _ a) (at level 0).  


    Section Semantics. 
    (* Unreliable Process Transition == Semantics *) 
    Inductive UPTransition (c:Channel) : Process -> Action c-> Process -> Prop := 
        | utTALK   : forall P(v:A c)(listener:Process), 
                      UPTransition c (TALK c v listener c P) !(Clear c v) listener
        | utLISTEN : forall (f:A c->Process)v p,        
                      UPTransition c (LISTEN c f) ? v p
        | utPAR    : forall p1 p2 q1 q2 v,            
                      UPTransition c p1 !(Clear c v) p2  -> 
                      UPTransition c q1 ? v q2 -> 
                      UPTransition c (PAR p1 q1) !(Clear c v) (PAR p2 q2). 

    End Semantics. 
    
    Section Properties. 
      Variable transition : forall c, Process -> Action c -> Process -> Prop. 

      Notation "p =( a ) c => q" := (transition c p a q)(at level 80,right associativity). 

      CoInductive SigStream : Type := 
        | Cons : forall c, Signal c -> SigStream -> SigStream. 

      Notation " x ::: xs " := (Cons _ x xs) (at level 90, right associativity). 

      Section Basics.
            (* Predicate P *) 
        Variable P : Process -> SigStream -> Prop. 

            (* Eventually Fail *) 
        Inductive Eventually : Process -> SigStream -> Prop := 
          | notyet :  forall p c (w:Signal c) s q, 
                      p =(!w)c=> q ->     
                      (forall q, p =(!w)c=> q -> ~ P p (w:::s) -> Eventually q s) -> 
                      Eventually p (w:::s) . 

        Inductive Always : Process -> SigStream -> Prop := 
          | always :  forall p c (w:Signal c) s, 
                      P p (w:::s) -> 
                      (forall q, p =(!w)c=> q -> Always q s) -> 
                      Always p (w:::s) .

        Theorem Eventually_stable : forall p s c (w:Signal c) q, 
          p =(!w)c=> q -> ~ P p (w:::s) -> Eventually p (w:::s) -> Eventually q s . 
        Proof. 
          intros. 
          inversion H1.    
          apply H7.
          - change ((fun cw : sigS Signal  => 
            let (c,w) := cw in p=(!w)c=>q) (existS _ c w1)). 
            now dependent rewrite H3. 
          - change ((fun cw : sigS Signal  => 
            let (c,w) := cw in ~ P p (w ::: s)) (existS _ c w1)).  
            now dependent rewrite H3. 
        Qed. 

        Theorem Always_stable : forall p s c (w:Signal c) q, 
          p =(!w)c=> q -> Always p (w:::s) -> Always q s . 
        Proof. 
          intros. 
          inversion H0. subst.
          apply H6. 
          change (( fun cw : sigS Signal => 
                  let (c,w) := cw in p=(!w)c=>q ) (existS _ c w1)). 
          now dependent rewrite H2. 
        Qed. 


      End Basics. 

      Section StillHappens. 

        Variable B : Set . 
        Variable P :      Process -> SigStream -> Prop. 
        Variable Q : B -> Process -> SigStream -> Prop. 

        Inductive Wittness b pn rs : Process -> SigStream -> Prop :=
          | goback :
              forall p ss c(w : Signal c) q,
              p =(! w)c=> q ->
              ~ Q b pn (w:::ss) ->
              Wittness b pn rs q ss -> Wittness b pn rs p (w:::ss)
          | start :
              forall cn (wn : Signal cn) p,
              p =(! wn)cn=> pn ->
              Q b pn (wn:::rs) -> Wittness b pn rs p (wn:::rs).

        Theorem StillHappens : forall b p ss q ss1,
          Wittness b q ss1 p ss -> Always P p ss -> Always P q ss1.
        Proof. 
          intros a p ss q ss1 H; elim H; intros.  
          - apply H3.
            now apply (Always_stable P p0 ss0 c w q0).
          - now apply (Always_stable P p0 ss1 cn wn q).
        Qed.




        (* This is a bad definition *) 
        Inductive Witness' (pn:Process)(rs:SigStream) : Process -> SigStream -> Prop :=
          | goback'  : forall p ss c (w:Signal c) q, 
              p =(!w)c=> q -> 
              ~ P pn (w:::ss) -> 
              Witness' pn rs q ss -> 
              Witness' pn rs p (w:::ss) 
          | start'   : forall p cn (wn:Signal cn) , 
              p =(!wn)cn=> pn -> 
              P pn (wn:::rs) ->              
              Witness' pn rs p (wn:::rs). (* t is the witness of the failure *)  

        Theorem StillHappens' : forall p ss q ss', 
              Witness' q ss' p ss -> Always P p ss -> Always P q ss'. 
        Proof. 
          intros p ss q ss' H; inversion H; subst. 
          - intros. 
        Abort. 

        End StillHappens. 
            




            




              


