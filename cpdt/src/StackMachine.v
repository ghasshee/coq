Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.
(** The second command above affects the default behavior of definitions regarding type inference, 
and the third allows for more concise pattern-matching syntax in Coq versions 8.5 and higher 
(having no effect in earlier versions). *)

Definition bleh := app_assoc.


Inductive binop : Set := Plus | Times.


Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.


Definition binopDenote b := match b with 
| Plus  => plus
| Times => mult
end.


Fixpoint expDenote e := match e with 
  | Const n         => n
  | Binop b e1 e2   => (binopDenote b)(expDenote e1)(expDenote e2) 
end.  



Eval simpl in expDenote (Const 42).
(** [= 42 : nat] *)

Eval simpl in expDenote (Binop Plus (Const 2) (Const 2)).
(** [= 4 : nat] *)

Eval simpl in expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).
(** [= 28 : nat] *)







(** stack machine **) 

Inductive instr : Set :=
| iConst : nat -> instr
| iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.



Definition instrDenote (i : instr) (s : stack) : option stack := match i with
    | iConst n => Some (n :: s)
    | iBinop b =>
      match s with
        | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
        | _ => None
      end
  end.


(** progDenote :: postfix list -> computation result stack or err **)

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
    | nil => Some s
    | i :: p' =>
      match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
      end
  end.


(** compile : prefix expression -> postfix list **)

Fixpoint compile (e : exp) : prog :=
  match e with
    | Const n => iConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
  end.



Eval simpl in compile (Const 42).
(** [= iConst 42 :: nil : prog] *)
Eval simpl in compile (Binop Plus (Const 2) (Const 2)).
(** [= iConst 2 :: iConst 2 :: iBinop Plus :: nil : prog] *)
Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).
(** [= iConst 7 :: iConst 2 :: iConst 2 :: iBinop Plus :: iBinop Times :: nil : prog] *)

(** %\smallskip{}%We can also run our compiled programs and check that they give the right results. *)
Eval simpl in progDenote (compile (Const 42)) nil.
(** [= Some (42 :: nil) : option stack] *)
Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))) nil.
(** [= Some (4 :: nil) : option stack] *)
Eval simpl in progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2))
  (Const 7))) nil.



Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
Abort.

Lemma compile_correct' : forall e p s,
  progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
  induction e.
  intros.
  unfold compile.
  unfold expDenote.
  unfold progDenote at 1.
  simpl.
  fold progDenote.
  reflexivity.
  intros.
  unfold compile.
  fold compile.
  unfold expDenote.
  fold expDenote.

Check app_assoc_reverse.
SearchRewrite ((_ ++ _) ++ _).

  rewrite app_assoc_reverse.
  rewrite IHe2.
  rewrite app_assoc_reverse.
  rewrite IHe1.
  unfold progDenote at 1.
  simpl.
  fold progDenote.
  reflexivity.

Abort.

(** %\index{tactics!induction}\index{tactics!crush}% *)

Lemma compile_correct' : forall e s p, progDenote (compile e ++ p) s =
  progDenote p (expDenote e :: s).
  induction e; crush.
Qed.


Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
  intros.


Check app_nil_end.


  rewrite (app_nil_end (compile e)).
  rewrite compile_correct'.
  reflexivity.
Qed.






(* 2.2 stack machine *) 

Inductive type : Set := 
| Nat 
| Bool.

(** Like most programming languages, Coq uses case-sensitive variable names, so that our user-defined type [type] is distinct from the [Type] keyword that we have already seen appear in the statement of a polymorphic theorem (and that we will meet in more detail later), and our constructor names [Nat] and [Bool] are distinct from the types [nat] and [bool] in the standard library.

   Now we define an expanded set of binary operators. *)

Inductive tybinop : type -> type -> type -> Set :=
| TyPlus  : tybinop Nat Nat Nat
| TyTimes : tybinop Nat Nat Nat
| TyEq    : forall t, tybinop t t Bool
| TyLt    : tybinop Nat Nat Bool.

(** The definition of [tbinop] is different from [binop] in an important way.  Where we declared that [binop] has type [Set], here we declare that [tbinop] has type [type -> type -> type -> Set].  We define [tbinop] as an _indexed type family_.  Indexed inductive types are at the heart of Coq's expressive power; almost everything else of interest is defined in terms of them.

The intuitive explanation of [tbinop] is that a [tbinop t1 t2 t] is a binary operator whose operands should have types [t1] and [t2], and whose result has type [t].  For instance, constructor [TLt] (for less-than comparison of numbers) is assigned type [tbinop Nat Nat Bool], meaning the operator's arguments are naturals and its result is Boolean.  The type of [TEq] introduces a small bit of additional complication via polymorphism: we want to allow equality comparison of any two values of any type, as long as they have the _same_ type.

ML and Haskell have indexed algebraic datatypes.  For instance, their list types are indexed by the type of data that the list carries.  However, compared to Coq, ML and Haskell 98 place two important restrictions on datatype definitions.

First, the indices of the range of each data constructor must be type variables bound at the top level of the datatype definition.  There is no way to do what we did here, where we, for instance, say that [TPlus] is a constructor building a [tbinop] whose indices are all fixed at [Nat].  %\index{generalized algebraic datatypes}\index{GADTs|see{generalized algebraic datatypes}}% _Generalized algebraic datatypes_ (GADTs)%~\cite{GADT}% are a popular feature in %\index{GHC Haskell}%GHC Haskell, OCaml 4, and other languages that removes this first restriction.

The second restriction is not lifted by GADTs.  In ML and Haskell, indices of types must be types and may not be _expressions_.  In Coq, types may be indexed by arbitrary Gallina terms.  Type indices can live in the same universe as programs, and we can compute with them just like regular programs.  Haskell supports a hobbled form of computation in type indices based on %\index{Haskell}%multi-parameter type classes, and recent extensions like type functions bring Haskell programming even closer to "real" functional programming with types, but, without dependent typing, there must always be a gap between how one programs with types and how one programs normally.
*)

(** We can define a similar type family for typed expressions, where a term of type [texp t] can be assigned object language type [t].  (It is conventional in the world of interactive theorem proving to call the language of the proof assistant the%\index{meta language}% _meta language_ and a language being formalized the%\index{object language}% _object language_.) *)

Inductive tyexp : type -> Set :=
| TyNatConst  : nat   -> tyexp Nat
| TyBoolConst : bool  -> tyexp Bool
| TyBinop     : forall t1 t2 t, tybinop t1 t2 t -> tyexp t1 -> tyexp t2 -> tyexp t.

(** Thanks to our use of dependent types, every well-typed [texp] represents a well-typed source expression, by construction.  This turns out to be very convenient for many things we might want to do with expressions.  For instance, it is easy to adapt our interpreter approach to defining semantics.  We start by defining a function mapping the types of our object language into Coq types: *)

Definition typeDenote (t : type) : Set :=
  match t with
    | Nat     => nat
    | Bool    => bool
  end.

(** It can take a few moments to come to terms with the fact that [Set], the type of types of programs, is itself a first-class type, and that we can write functions that return [Set]s.  Past that wrinkle, the definition of [typeDenote] is trivial, relying on the [nat] and [bool] types from the Coq standard library.  We can interpret binary operators by relying on standard-library equality test functions [eqb] and [beq_nat] for Booleans and naturals, respectively, along with a less-than test [leb]: *)

Definition tybinopDenote arg1 arg2 res (b : tybinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
    | TyPlus      => plus
    | TyTimes     => mult
    | TyEq Nat    => beq_nat
    | TyEq Bool   => eqb
    | TyLt        => leb
  end.

(** This function has just a few differences from the denotation functions we saw earlier.  First, [tbinop] is an indexed type, so its indices become additional arguments to [tbinopDenote].  Second, we need to perform a genuine%\index{dependent pattern matching}% _dependent pattern match_, where the necessary _type_ of each case body depends on the _value_ that has been matched.  At this early stage, we will not go into detail on the many subtle aspects of Gallina that support dependent pattern-matching, but the subject is central to Part II of the book.

The same tricks suffice to define an expression denotation function in an unsurprising way.  Note that the [type] arguments to the [TBinop] constructor must be included explicitly in pattern-matching, but here we write underscores because we do not need to refer to those arguments directly. *)

Fixpoint tyexpDenote t (e : tyexp t) : typeDenote t :=
  match e with
    | TyNatConst n          => n
    | TyBoolConst b         => b
    | TyBinop _ _ _ b e1 e2 => (tybinopDenote b) (tyexpDenote e1) (tyexpDenote e2)
  end.

(** We can evaluate a few example programs to convince ourselves that this semantics is correct. *)

Eval simpl in tyexpDenote (TyNatConst 42).
(** [= 42 : typeDenote Nat] *)

(* begin hide *)
Eval simpl in tyexpDenote (TyBoolConst false).
(* end hide *)
Eval simpl in tyexpDenote (TyBoolConst true).
(** [= true : typeDenote Bool] *)

Eval simpl in tyexpDenote (TyBinop TyTimes (TyBinop TyPlus (TyNatConst 2) (TyNatConst 2)) (TyNatConst 7)).
(** [= 28 : typeDenote Nat] *)

Eval simpl in tyexpDenote (TyBinop (TyEq Nat) (TyBinop TyPlus (TyNatConst 2) (TyNatConst 2)) (TyNatConst 7)).
(** [= false : typeDenote Bool] *)

Eval simpl in tyexpDenote (TyBinop TyLt (TyBinop TyPlus (TyNatConst 2) (TyNatConst 2))(TyNatConst 7)).
(** [= true : typeDenote Bool] *)



Definition tystack := list type.

Inductive tyinstr : tystack -> tystack -> Set :=
| TiNConst  : forall s,               nat                   -> tyinstr s (Nat::s)
| TiBConst  : forall s,               bool                  -> tyinstr s (Bool::s)
| TiBinop   : forall arg1 arg2 res s, tybinop arg1 arg2 res -> tyinstr (arg1::arg2::s) (res::s).

Inductive typrog : tystack -> tystack -> Set :=
| TyNil     : forall s,               typrog s s
| TyCons    : forall s1 s2 s3,        tyinstr s1 s2 -> typrog s2 s3 -> typrog s1 s3.

(* Semantics of the new language *) 
Fixpoint vstack (ts : tystack) : Set :=
  match ts with
    | nil       => unit
    | t :: ts'  => typeDenote t * vstack ts'
  end%type.  (* '%type' ensures that '*' is not multiplication but cartesian-product *) 

Definition tyinstrDenote ts ts' (i : tyinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
    | TiNConst _ n      => fun s => (n, s)
    | TiBConst _ b      => fun s => (b, s)
    | TiBinop _ _ _ _ b => fun s => let '(arg1, (arg2, s')) := s in 
                                    ((tybinopDenote b) arg1 arg2, s')
  end.


Fixpoint typrogDenote ts ts' (p : typrog ts ts') : vstack ts -> vstack ts' :=
  match p with
    | TyNil _           => fun s => s
    | TyCons _ _ _ i p' => fun s => typrogDenote p' (tyinstrDenote i s)
  end.



(* concatenate two stack machine programs *)
Fixpoint tyconcat ts ts' ts'' (p : typrog ts ts') : typrog ts' ts'' -> typrog ts ts'' :=
  match p with
    | TyNil _            => fun p' => p'
    | TyCons _ _ _ i p1  => fun p' => TyCons i (tyconcat p1 p')
  end.


Fixpoint tycompile t (e : tyexp t) (ts : tystack) : typrog ts (t :: ts) :=
  match e with
    | TyNatConst n          => TyCons (TiNConst _ n) (TyNil _)
    | TyBoolConst b         => TyCons (TiBConst _ b) (TyNil _)
    | TyBinop _ _ _ b e1 e2 => tyconcat (tycompile e2 _)
      (tyconcat (tycompile e1 _) (TyCons (TiBinop _ b) (TyNil _)))
  end.

(* Coq can have _ (underscore at righthand side of matchin *) 
(* Print can show what is inserted to it. *)
Print tycompile.

(** %\vspace{-.15in}%[[
tcompile = 
fix tcompile (t : type) (e : texp t) (ts : tstack) {struct e} :
  tprog ts (t :: ts) :=
  match e in (texp t0) return (tprog ts (t0 :: ts)) with
  | TNConst n => TCons (TiNConst ts n) (TNil (Nat :: ts))
  | TBConst b => TCons (TiBConst ts b) (TNil (Bool :: ts))
  | TBinop arg1 arg2 res b e1 e2 =>
      tconcat (tcompile arg2 e2 ts)
        (tconcat (tcompile arg1 e1 (arg2 :: ts))
           (TCons (TiBinop ts b) (TNil (res :: ts))))
  end
     : forall t : type, texp t -> forall ts : tstack, tprog ts (t :: ts)
]]
*)



(* 'tt' is unit or () in OCaml *) 
Eval simpl in typrogDenote (tycompile (TyNatConst 42) nil) tt.
(** [= (42, tt) : vstack (Nat :: nil)] *)

Eval simpl in typrogDenote (tycompile (TyBoolConst true) nil) tt.
(** [= (true, tt) : vstack (Bool :: nil)] *)

Eval simpl in typrogDenote (tycompile (TyBinop TyTimes (TyBinop TyPlus (TyNatConst 2)
  (TyNatConst 2)) (TyNatConst 7)) nil) tt.
(** [= (28, tt) : vstack (Nat :: nil)] *)

Eval simpl in typrogDenote (tycompile (TyBinop (TyEq Nat) (TyBinop TyPlus (TyNatConst 2)
  (TyNatConst 2)) (TyNatConst 7)) nil) tt.
(** [= (false, tt) : vstack (Bool :: nil)] *)

Eval simpl in typrogDenote (tycompile (TyBinop TyLt (TyBinop TyPlus (TyNatConst 2) (TyNatConst 2))
  (TyNatConst 7)) nil) tt.
(** [= (true, tt) : vstack (Bool :: nil)] *)

(** %\smallskip{}%The compiler seems to be working, so let us turn to proving that it _always_ works. *)


(** ** Translation Correctness *)

(** We can state a correctness theorem similar to the last one. *)

Theorem tycompile_correct : forall t (e : tyexp t),
  typrogDenote (tycompile e nil) tt = (tyexpDenote e, tt).


Abort.




Lemma tycompile_correct' : forall t (e : tyexp t) ts (s : vstack ts),
  typrogDenote (tycompile e ts) s = (tyexpDenote e, s).

(** While lemma [compile_correct'] quantified over a program that is the "continuation"%~\cite{continuations}% for the expression we are considering, here we avoid drawing in any extra syntactic elements.  In addition to the source expression and its type, we also quantify over an initial stack type and a stack compatible with it.  Running the compilation of the program starting from that stack, we should arrive at a stack that differs only in having the program's denotation pushed onto it.

   Let us try to prove this theorem in the same way that we settled on in the last section. *)

  induction e; crush.

(** We are left with this unproved conclusion:

[[
tprogDenote
     (tconcat (tcompile e2 ts)
        (tconcat (tcompile e1 (arg2 :: ts))
           (TCons (TiBinop ts t) (TNil (res :: ts))))) s =
   (tbinopDenote t (texpDenote e1) (texpDenote e2), s)
 
]]

We need an analogue to the [app_assoc_reverse] theorem that we used to rewrite the goal in the last section.  We can abort this proof and prove such a lemma about [tconcat].
*)

Abort.

Lemma tyconcat_correct : forall ts ts' ts'' (p : typrog ts ts') (p' : typrog ts' ts'')
  (s : vstack ts),
  typrogDenote (tyconcat p p') s
  = typrogDenote p' (typrogDenote p s).
  induction p; crush.
Qed.

(** This one goes through completely automatically.

Some code behind the scenes registers [app_assoc_reverse] for use by [crush].  We must register [tconcat_correct] similarly to get the same effect:%\index{Vernacular commands!Hint Rewrite}% *)

Hint Rewrite tyconcat_correct.

(** Here we meet the pervasive concept of a _hint_.  Many proofs can be found through exhaustive enumerations of combinations of possible proof steps; hints provide the set of steps to consider.  The tactic [crush] is applying such brute force search for us silently, and it will consider more possibilities as we add more hints.  This particular hint asks that the lemma be used for left-to-right rewriting.

Now we are ready to return to [tcompile_correct'], proving it automatically this time. *)

Lemma tycompile_correct' : forall t (e : tyexp t) ts (s : vstack ts),
  typrogDenote (tycompile e ts) s = (tyexpDenote e, s).

induction e.
unfold tyexpDenote.
unfold tycompile.
unfold typrogDenote.
unfold tyinstrDenote.
reflexivity.

unfold tyexpDenote.
unfold tycompile.
unfold typrogDenote.
unfold tyinstrDenote.
reflexivity.

simpl.
intros.
unfold tyconcat at 2.
rewrite tyconcat_correct.
fold tyconcat.
rewrite IHe2.
rewrite tyconcat_correct.
unfold typrogDenote at 1.
unfold tyinstrDenote.

rewrite IHe1.
reflexivity.

Qed.

(** We can register this main lemma as another hint, allowing us to prove the final theorem trivially. *)

Hint Rewrite tycompile_correct'.

Theorem tycompile_correct : forall t (e : tyexp t),
  typrogDenote (tycompile e nil) tt = (tyexpDenote e, tt).
  crush.
Qed.
(* end thide *)

(** It is probably worth emphasizing that we are doing more than building mathematical models.  Our compilers are functional programs that can be executed efficiently.  One strategy for doing so is based on%\index{program extraction}% _program extraction_, which generates OCaml code from Coq developments.

  To set up the feature properly in recent versions of Coq, we must run the command [Require Extraction.].  However, this book %PDF%#HTML# is still built with a patched old version of Coq that neither requires nor allows that command, so it is commented out in this rendering!

  Now we run a command to output the OCaml version of [tcompile]:%\index{Vernacular commands!Extraction}% *)

Require Extraction.
Extraction tycompile.

(** <<
let rec tcompile t e ts =
  match e with
  | TNConst n ->
    TCons (ts, (Cons (Nat, ts)), (Cons (Nat, ts)), (TiNConst (ts, n)), (TNil
      (Cons (Nat, ts))))
  | TBConst b ->
    TCons (ts, (Cons (Bool, ts)), (Cons (Bool, ts)), (TiBConst (ts, b)),
      (TNil (Cons (Bool, ts))))
  | TBinop (t1, t2, t0, b, e1, e2) ->
    tconcat ts (Cons (t2, ts)) (Cons (t0, ts)) (tcompile t2 e2 ts)
      (tconcat (Cons (t2, ts)) (Cons (t1, (Cons (t2, ts)))) (Cons (t0, ts))
        (tcompile t1 e1 (Cons (t2, ts))) (TCons ((Cons (t1, (Cons (t2,
        ts)))), (Cons (t0, ts)), (Cons (t0, ts)), (TiBinop (t1, t2, t0, ts,
        b)), (TNil (Cons (t0, ts))))))
>>

We can compile this code with the usual OCaml compiler and obtain an executable program with halfway decent performance.

This chapter has been a whirlwind tour through two examples of the style of Coq development that I advocate.  Parts II and III of the book focus on the key elements of that style, namely dependent types and scripted proof automation, respectively.  Before we get there, we will spend some time in Part I on more standard foundational material.  Part I may still be of interest to seasoned Coq hackers, since I follow the highly automated proof style even at that early stage. *)
