(***********************************************************************)
(** * Typing rules for STLC *)
(***********************************************************************)

(** This file containes definitions for the typing rules for a locally-nameless
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

Require Import Stlc.DefinitionsSyntax.
Require Export Stlc.ClassInstances.
Import SyntaxNotations.
Open Scope syntax_scope.

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
