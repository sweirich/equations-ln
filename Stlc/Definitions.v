(***********************************************************************)
(** * Definition of STLC *)
(***********************************************************************)

(** This file containes definitions for a locally-nameless
    representation of a Curry-Style simply-typed lambda calculus.
*)


Require Import Metalib.Metatheory.
Require Import Metalib.LibLNgen.

Require Import Utf8 Arith Compare_dec Lia.

(* equations *)
Set Warnings "-notation-overridden".
Require Import Relation_Operators Program.
Close Scope program_scope.
From Equations Require Import Equations.

Require Export Stlc.Fin.
Require Export Stlc.Classes.
Import SyntaxNotations.
Open Scope syntax_scope.

(***********************************************************************)
(** * Syntax of STLC *)
(***********************************************************************)

(** We use a locally nameless representation for the simply-typed lambda
    calculus, where bound variables are represented as natural numbers
    (de Bruijn indices) and free variables are represented as [atom]s.

    The type [atom], defined in the Metatheory library, represents names.
    Equality on names is decidable, and it is possible to generate an
    atom fresh for any given finite set of atoms ([atom_fresh]).

    Note: the type [var] is notation for [atom].  *)

Inductive typ : Set :=  (*r types *)
 | typ_base : typ
 | typ_arrow (T1:typ) (T2:typ).

Scheme Equality for typ.

(* Expressions are indexed by the number of *bound variables*
   that appear in terms. *)

Definition v (e : nat -> Set) := var.

Inductive exp : nat ->  Set :=  (*r expressions *)
 | var_b : forall {n}, fin n -> exp n
 | var_f : forall {n} (x:var), exp n
 | abs   : forall {n} (e:exp (S n)), exp n
 | app   : forall {n} (e1:exp n) (e2:exp n), exp n.

(* Cargo culting equations *)
Derive Signature NoConfusion NoConfusionHom for exp.

(* like an inversion tactic for equalities *)
Ltac noconf_exp := 
  match goal with 
    | [ H : var_b _ = var_b _ |- _ ] => noconf H
    | [ H : var_f _ = var_f _ |- _ ] => noconf H
    | [ H : abs _ = abs _ |- _ ] => noconf H
    | [ H : app _ _ = app _ _ |- _ ] => noconf H
  end.

(* We cannot derive decidable equality automatically, but 
   we can define it. *)
(* Decidable equality for expressions *)
Equations exp_eq_dec {n} (e1 : exp n) (e2: exp n) : { e1 = e2 } + { e1 <> e2 } := 
 exp_eq_dec (var_b m1) (var_b m2) with eq_dec m1 m2 =>  {
      exp_eq_dec _ _ (left eq_refl) := left _ ; 
      exp_eq_dec _ _ (right p) := in_right } ; 

 exp_eq_dec (var_f x1) (var_f x2) with EqDec_eq_of_X x1 x2 => {
      exp_eq_dec (var_f x1) (var_f x2) (left eq_refl) := left _ ; 
      exp_eq_dec (var_f x2) (var_f x2) (right p) := in_right } ; 

 exp_eq_dec (abs e1) (abs e2) with exp_eq_dec e1 e2  => {
      exp_eq_dec _ _ (left eq_refl) := left _ ; 
      exp_eq_dec _ _ (right p) := in_right } ; 

 exp_eq_dec (app e1 e2) (app e3 e4) 
   with (exp_eq_dec e1 e3, exp_eq_dec e2 e4) => {
      exp_eq_dec _ _ (left eq_refl , left eq_refl) := left _ ; 
      exp_eq_dec _ _ (right p, left eq_refl) := in_right ;
      exp_eq_dec _ _ (_ , right p) := in_right } ; 

 exp_eq_dec  _  _ := in_right.

(* Calculate the size of an expression. We could do this 
   with equations, but it is simple enough not to. *)
Fixpoint size_exp {n} (e1 : exp n) : nat :=
  match e1 with
    | abs e2 => 1 + (size_exp e2)
    | var_f x1 => 1
    | var_b m => 1
    | app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
  end.

(***********************************************************************)
(** * Substitution *)
(***********************************************************************)

(** Substitution replaces a free variable with a term.  The definition below
    is simple because bound variables are represented using indices. As a
    result, there is no need to worry about variable capture.  *)

(** 
    Note that [subst_exp] uses [x == y] for decidable equality.
    This operation is defined in the Metatheory library. 
    
    This definition is defined for *all* scoping levels of the term we are 
    substituting into. However, the replacement for y (i.e. the expression u)
    must be compatible with the scoping level for e. 
    As a result, we weaken u when going under a binder.

 *)

(* Weaken the number of binders allowed in an expression by 1 *)
Equations weaken_exp {n} (e : exp n): exp (S n):= {
  weaken_exp  (var_b m) => var_b (increase_fin m);
  weaken_exp  (var_f x) => var_f x;
  weaken_exp  (abs t)   => abs (weaken_exp t);
  weaken_exp  (app f t) => app (weaken_exp f) (weaken_exp t)
  }.

(* Substitute for a free variable. *)
Equations subst_exp_wrt_exp {n} (u:exp n) (y:var) (e:exp n) : exp n :=
  subst_exp_wrt_exp u y (var_b m)   := var_b m;
  subst_exp_wrt_exp u y (var_f x)   := if x == y then u else var_f x;
  subst_exp_wrt_exp u y (abs e1)    := 
    abs (subst_exp_wrt_exp (weaken_exp u) y e1);
  subst_exp_wrt_exp u y (app e1 e2) := 
    app (subst_exp_wrt_exp u y e1) (subst_exp_wrt_exp u y e2).

(***********************************************************************)
(** * Free variables *)
(***********************************************************************)

(** The function [fv_exp], defined below, calculates the set of free
    variables in an expression.  Because we are using a locally
    nameless representation, where bound variables are represented as
    indices, any name we see is a free variable of a term.  In
    particular, this makes the [abs] case simple.
*)

Fixpoint fv_exp {n} (e_5:exp n) : vars :=
  match e_5 with
  | (var_b m)   => {}
  | (var_f x)   => {{x}}
  | (abs e)     => fv_exp e
  | (app e1 e2) => fv_exp e1 `union` fv_exp e2
end.

(** The type [vars] represents a finite set of elements of type [atom].
    The notations for the finite set definitions (empty set `{}`,
    singleton `{{x}}` and union `\u`) is also defined in the Metatheory
    library.  *)


(***********************************************************************)
(** * Opening *)
(***********************************************************************)

(** Opening replaces an index with a term.  It corresponds to informal
    substitution for a bound variable, such as in the rule for beta reduction.
    Note that only "dangling" indices (those that do not refer to any
    abstraction) can be opened, so the index of [exp] must be at least 1.

    In the bound variable case, we check to see if the fin is 0 using
    [decrease_fin]. If it is zero, we found the place for [u].  If it is
    nonzero, we get the same value in a smaller scope.

    We assume that the argument [u] has one fewer "dangling" index than the
    term that we are opening. As with [subst] we need to weaken this term when
    we go under a binder.  *)


Equations open_exp_wrt_exp {k:nat} (u:exp k) (e:exp (S k)) : exp k :=
  open_exp_wrt_exp u (var_b m) :=
     match decrease_fin k m with
        | None => u
        | Some f => var_b f
      end;
  open_exp_wrt_exp u (var_f x)   := var_f x;
  open_exp_wrt_exp u (abs e)     := 
    abs (open_exp_wrt_exp (weaken_exp u) e);
  open_exp_wrt_exp u (app e1 e2) := 
    app (open_exp_wrt_exp u e1) (open_exp_wrt_exp u e2).

(* Close *)

(** Closing an expression means replacing a free variable x1 with a new bound
   variable.  This increases the binding depth of the expression by 1.
   Existing bound variables must be weakened to the new scope, using
   [increase_fin]. Where we find a free variable that should be bound, we
   introduce it at the current binding depth using [gof].  *)

Equations close_exp_wrt_exp {k : nat} (x1 : var) (e1 : exp k) : exp (S k) :=
  close_exp_wrt_exp x1 (var_b m) := 
    var_b (increase_fin m);
  close_exp_wrt_exp x1 (@var_f k x2) := 
    if (x1 == x2) then (var_b (gof k)) else (var_f x2);
  close_exp_wrt_exp x1 (abs e2) := 
    abs (close_exp_wrt_exp x1 e2);
  close_exp_wrt_exp x1 (app e2 e3) := 
    app (close_exp_wrt_exp x1 e2) (close_exp_wrt_exp x1 e3).

(***********************************************************************)
(** * Class  instances *)
(***********************************************************************)

#[global] Instance Syntax_exp : Syntax exp := { 
    fv := fun {n} => @fv_exp n;
    size := fun {n} => @size_exp n; 
    weaken := fun {n} =>  @weaken_exp n;
    close := fun {n} => @close_exp_wrt_exp n;
}.

#[global] Opaque Syntax_exp.

#[global] Instance Subst_exp : Subst exp exp := {
    open := fun {n} => @open_exp_wrt_exp n;
    subst := fun {n} => @subst_exp_wrt_exp n
}.
#[global] Opaque Subst_exp.

(***********************************************************************)
(** * Typing contexts *)
(***********************************************************************)

(** We represent typing contexts as association lists (lists of pairs of
    keys and values) whose keys are [atom]s.
*)

Definition ctx : Set := list (atom * typ).

(** For STLC, contexts bind [atom]s to [typ]s.

    Lists are defined in Coq's standard library, with the constructors
    [nil] and [cons].  The list library includes the [::] notation for
    cons as well as standard list operations such as append, map, and
    fold. The infix operation [++] is list append.

    The Metatheory library extends this reasoning by instantiating the
    AssocList library to provide support for association lists whose keys
    are [atom]s.  Everything in this library is polymorphic over the type
    of objects bound in the environment.  Look in AssocList.v for
    additional details about the functions and predicates that we mention
    below.  *)


(***********************************************************************)
(** * Typing relation *)
(***********************************************************************)

(** The definition of the typing relation is straightforward.  In
    order to ensure that the relation holds for only well-formed
    environments, we check in the [typing_var] case that the
    environment is [uniq].  The structure of typing derivations
    implicitly ensures that the relation holds only for locally closed
    expressions.

    Finally, note the use of cofinite quantification in
    the [typing_abs] case.
*)

Inductive typing : ctx -> exp 0 -> typ -> Prop :=
 | typing_var : forall (G:ctx) (x:atom) (T:typ),
     uniq G ->
     binds x T G  ->
     typing G (var_f x) T
 | typing_abs : forall (L:vars) (G:ctx) (T1:typ) (e:exp 1) (T2:typ),
     (forall x , x `notin` L -> typing ([(x,T1)] ++ G) (e ^ var_f x) T2)  ->
     typing G (abs e) (typ_arrow T1 T2)
 | typing_app : forall (G:ctx) (e1 e2:exp 0) (T2 T1:typ),
     typing G e1 (typ_arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (app e1 e2) T2 .

Derive Signature for typing.

(***********************************************************************)
(** * Values and Small-step Evaluation *)
(***********************************************************************)

(** Finally, we define values and a call-by-name small-step evaluation
    relation. In STLC, abstractions are the only value. *)

Definition is_value (e : exp 0) : Prop :=
  match e with
  | abs _   => True
  | _       => False
  end.

(** For [step_beta], note that we use [open_exp_wrt_exp] instead of
    substitution --- no variable names are involved.

    Note also the hypotheses in [step] that ensure that the relation holds
    only for locally closed terms.  *)

Inductive step : exp 0 -> exp 0 -> Prop :=
 | step_beta : forall (e1:exp 1)(e2:exp 0),
     step (app (abs e1) e2) (e1 ^ e2)
 | step_app : forall (e1 e2 e1':exp 0),
     step e1 e1' ->
     step (app e1 e2) (app e1' e2).

Derive Signature for step.

#[global] Hint Constructors typing step : core.
