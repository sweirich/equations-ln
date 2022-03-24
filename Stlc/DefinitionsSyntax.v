(***********************************************************************)
(** * Definition of STLC *)
(***********************************************************************)

(** This file containes definitions for a locally-nameless
    representation of a Curry-Style simply-typed lambda calculus.
*)


Require Import Metalib.Metatheory.

Require Import Utf8 Arith Compare_dec Lia.
(* equations *)
Set Warnings "-notation-overridden".
Require Import Relation_Operators Program.
Close Scope program_scope.
From Equations Require Import Equations.

Require Export Stlc.Fin.

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

Inductive exp : nat ->  Set :=  (*r expressions *)
 | var_b : forall {n}, fin n -> exp n
 | var_f : forall {n} (x:var), exp n
 | abs   : forall {n} (e:exp (S n)), exp n
 | app   : forall {n} (e1:exp n) (e2:exp n), exp n.

(* [Signature] creates a sigma type that allowing packing values with their
   constructor index.

   [NoConfusion] creates a heterogenous relation that defines injectivity and
   discrimination of constructors: That is, two values with the same
   constructor are equal if their arguments are also equal. [NoConfusionHom]
   produces a homogenous relation of the same. *)
Derive Signature NoConfusion NoConfusionHom for exp.

(* This should be part of metalib *)
#[local] Instance Atom_EqDec : EqDec Atom.atom := Atom.eq_dec.

(* Decidable equality for expressions *)
Derive Subterm EqDec for exp.

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

(* Weaken the number of bound variables allowed in an expression by 1 *)

Equations weaken_exp {n} (e : exp n): exp (S n):= {
  weaken_exp  (var_b m) => var_b (increase_fin m);
  weaken_exp  (var_f x) => var_f x;
  weaken_exp  (abs t)   => abs (weaken_exp t);
  weaken_exp  (app f t) => app (weaken_exp f) (weaken_exp t)
  }. 

(* Can also write this as a Fixpoint. But, let's do everything with 
   equations*)
(*
Fixpoint weaken_exp {n} (e : exp n) : exp (S n) :=
  match e with 
  | var_b m => var_b (increase_fin m)
  | var_f x => var_f x
  | abs t => abs (weaken_exp t)
  | app f t => app (weaken_exp f) (weaken_exp t)
  end. *)

(* Substitute for a free variable. *)
Equations subst_exp_wrt_exp {n} (u:exp n) (y:var) (e:exp n) : exp n :=
  subst_exp_wrt_exp u y (var_b m)   := 
    var_b m;
  subst_exp_wrt_exp u y (var_f x)   := 
    if x == y then u else var_f x;
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

(* This is only correct if we call it with exp 0 *)

Equations open_exp_wrt_exp {k:nat} (u:exp k) (e:exp (S k)) : exp k :=
  open_exp_wrt_exp u (var_b m) with decrease_fin k m := {
    | None => u
    | Some f => var_b f
    };
  open_exp_wrt_exp u (var_f x)   := var_f x;
  open_exp_wrt_exp u (abs e)     := 
    abs (open_exp_wrt_exp (weaken_exp u) e);
  open_exp_wrt_exp u (app e1 e2) := 
    app (open_exp_wrt_exp u e1) (open_exp_wrt_exp u e2).

(*
ALTERNATIVE approach.

Equations open_exp_wrt_exp {k:nat} (u:exp 0) (e:exp (S k)) : exp k :=
  open_exp_wrt_exp u (var_b m) :=
     match decrease_fin k m with
        | None => (weaken_exp_by k u)
        | Some f => var_b f
      end;
  open_exp_wrt_exp u (var_f x)   := var_f x;
  open_exp_wrt_exp u (abs e)     := 
    abs (open_exp_wrt_exp u e);
  open_exp_wrt_exp u (app e1 e2) := 
    app (open_exp_wrt_exp u e1) (open_exp_wrt_exp u e2).
*)

(*
Fixpoint open_exp_wrt_exp {k:nat} (u:exp k) 
         (e:exp (S k)) : exp k :=
  match e with 
  | var_b m => match decrease_fin k m with
        | None => u
        | Some f => var_b f
      end
  | (var_f x) => var_f x
  | (abs e)   =>
      abs (open_exp_wrt_exp (weaken_exp u) e)
  | (app e1 e2) =>
    app (open_exp_wrt_exp u e1) (open_exp_wrt_exp u e2)
  end.
*)

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
