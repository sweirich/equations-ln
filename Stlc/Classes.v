Require Import Metalib.Metatheory.
Require Import Metalib.LibLNgen.
From Equations Require Import Equations.

(***********************************************************************)
(** * Notations *)
(***********************************************************************)

Class Syntax (e : nat -> Set) := {
   (* 
      To state the lemmas generically, we need to know 
      the free variable constructor of the datatype.
      (And use this overloaded term consistently through the 
      definitions of the language.)
    *)
    fv : forall {n}, e n -> vars ;
    size : forall {n}, e n -> nat ;
    weaken : forall {n}, e n -> e (S n) ;
    close : forall {n}, atom -> e n -> e (S n) ;
    open  : forall {n}, e n -> e (S n) -> e n ;
    subst : forall {n}, e n -> atom -> e n -> e n
}.

(***********************************************************************)
(** * Theory *)
(***********************************************************************)

(* These are the general form of the lemmas in the Lemmas.v file; and 
   perhaps automatically proven by a future version of LNgen. *)
   

Class SyntaxTheory (exp : nat -> Set) (evar : forall {n}, atom -> exp n) `{H: Syntax exp } := {

   size_weaken : forall n (t : exp n), size (weaken t) = size t;

   fv_weaken : forall n1 (e1 : exp n1), fv (weaken e1) = fv e1;

   size_min : forall n (e : exp n), 1 <= size e;

   size_close : forall n (e1 : exp n) x1, 
      size (close x1 e1) = size e1;

   size_open : (forall k (e1 : exp (S k)) (e2 : exp k),
      size e1 <= size (open e2 e1));

   size_open_var : (forall k (e : exp (S k)) x,
      size (open (evar x) e) = size e);

   close_inj : (forall k (e1 : exp k) e2 x1,
      close x1 e1 = close x1 e2 ->
      e1 = e2);

   close_open : (forall n1 (e1 : exp (S n1)) x1 ,
      x1 `notin` fv e1 ->
      close x1 (open (evar x1) e1) = e1);

   open_close : (forall n1 (e1 : exp n1) x1,
      open (evar x1) (close x1 e1) = e1);

   open_inj : (forall n1 (e2 e1:exp (S n1)) x1,
      x1 `notin` fv e2 ->
      x1 `notin` fv e1 ->
      open (evar x1) e2 = open (evar x1) e1 ->
      e2 = e1);

   (* TODO: add more *)

   subst_intro  : forall n (e1 : exp (S n)) (x1:atom) (e2 : exp n),
      x1 `notin` fv e1 ->
      open e2 e1 = subst e2 x1 (open (evar x1) e1) ;

   subst_open_var : forall n1 (e2 : exp (S n1)) e1 x1 x2,
        x1 <> x2 ->
        open (evar x2) (subst (weaken e1) x1 e2) = 
          subst e1 x1 (open (evar x2) e2)
   }.

(* TODO: rewriting/hint database for the above lemmas. *)


Create HintDb syntax.

Hint Rewrite (fun {e} {v} `{K:SyntaxTheory e v} => @close_open e v _ _) 
  using solve [auto; try typeclasses eauto] : syntax.

Hint Rewrite (fun {e} {v} `{K:SyntaxTheory e v} => @open_close e v _ _) 
  using solve [auto; try typeclasses eauto] : syntax.

Hint Rewrite (fun {e} {v} `{K:SyntaxTheory e v} => @subst_open_var e v _ _) 
  using solve [auto; try typeclasses eauto] : syntax.

(***********************************************************************)
(** * Rewriting / tactics *)
(***********************************************************************)


Create HintDb fv.
Create HintDb open.
Create HintDb close.
Create HintDb weaken.
Create HintDb size.
Create HintDb subst.

Ltac simp_syntax := repeat first [ 
                       simp subst
                     || simp open
                     || simp close
                     || simp weaken
                     || simp size
                     || simp fv
                     ].



(***********************************************************************)
(** * Notations *)
(***********************************************************************)

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definition provides a
    convenient shorthand for such uses.  Note that the order of
    arguments is switched relative to the definition above.  For
    example, [e ^ x] can be read as "substitute the variable [x]
    for index [0] in [e]".
*)

Declare Scope syntax_scope.
Module SyntaxNotations.
Notation "[ z ~> u ] e" := (subst u z e) (at level 0) : syntax_scope.
Notation "e ^ x"        := (open x e) : syntax_scope.
End SyntaxNotations.


