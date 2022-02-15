(***********************************************************************)
(** * Definition of STLC *)
(***********************************************************************)

(** This file containes all of the definitions for a locally-nameless
    representation of a Curry-Style simply-typed lambda calculus.

    This file was generated via Ott from `stlc.ott` and then edited to
    include explanation about the definitions. As a result, it is gathers
    all of the STLC definitions in one place, but the associated
    exercises are found elsewhere in the tutorial.  You'll want to refer
    back to this file as you progress through the rest of the
    material. *)


Require Import Metalib.Metatheory.
Require Import Metalib.LibLNgen.

(* ssreflect *)
From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Utf8 Arith Compare_dec Lia.

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

(*  produces 

typ_eq_dec
     : forall x y : typ, {x = y} + {x <> y}
*)


Inductive exp : nat ->  Set :=  (*r expressions *)
 | var_b : forall {n}, fin n -> exp n
 | var_f : forall {n} (x:var), exp n
 | abs   : forall {n} (e:exp (S n)), exp n
 | app   : forall {n} (e1:exp n) (e2:exp n), exp n.

(* Cargo culting equations *)
Derive Signature NoConfusion NoConfusionHom for exp.

(*
Equations exp_beq {n} (e1 : exp n) (e2: exp n) : bool :=
 exp_beq (var_b m1) (var_b m2) := fin_beq m1 m2 ;
 exp_beq (var_f x1) (var_f x2) := eqb x1 x2 ;
 exp_beq (abs e1) (abs e2) :=  exp_beq e1 e2 ;
 exp_beq (app e1 e2) (app e3 e4) := andb (exp_beq e1 e3) (exp_beq e2 e4);
 exp_beq  _  _ := false.
*)

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

(* Extraction exp_eq_dec. *)

(* The size of an expression *)
Fixpoint size_exp {n} (e1 : exp n) : nat :=
  match e1 with
    | abs e2 => 1 + (size_exp e2)
    | var_f x1 => 1
    | var_b m => 1
    | app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
  end.

(* Weaken the number of binders allowed in an expression *)
Equations weaken_exp {n} (e : exp n): exp (S n):= {
  weaken_exp  (var_b m) => var_b (increase_fin m);
  weaken_exp  (var_f x) => var_f x;
  weaken_exp  (abs t)   => abs (weaken_exp t);
  weaken_exp  (app f t) => app (weaken_exp f)(weaken_exp t)
  }.

(* Weakening *)
    
(* 
Equations weaken {n} m (e: exp n) : exp (n+m) :=
  weaken m (var_b m0) := var_b (weaken_fin m m0);
  weaken m (var_f x) :=  var_f x;
  weaken m (abs e) := abs  (weaken m e);
  weaken m (app e1 e2) := app (weaken m e1) (weaken m e2).

Lemma size_exp_weaken :
(forall n1 (e1 : exp n1) m,
  size_exp (weaken m e1) = size_exp e1).
Proof.
  intros n1 e1 m.
  funelim (weaken m e1); program_simpl.
Qed.

#[global] Hint Resolve size_exp_weaken : lngen.
Hint Rewrite size_exp_weaken using solve [auto] : lngen. 
*)

(* Close *)

(* Closing an expression means replacing a free variable x1 with a new bound variable. 
   This increases the binding depth of the expression. 
   Existing bound variables must be weakened to the new scope. Where we find a new 
   free variable, we introduce it at the current binding depth using gof.
 *)

Equations close_exp_wrt_exp_rec {k : nat} (x1 : var) (e1 : exp k) : exp (S k) :=
  close_exp_wrt_exp_rec x1 (var_b m) := 
    var_b (increase_fin m);
  close_exp_wrt_exp_rec x1 (@var_f k x2) := 
    if (x1 == x2) then (var_b (gof k)) else (var_f x2);
  close_exp_wrt_exp_rec x1 (abs e2) := 
    abs (close_exp_wrt_exp_rec x1 e2);
  close_exp_wrt_exp_rec x1 (app e2 e3) := 
    app (close_exp_wrt_exp_rec x1 e2) (close_exp_wrt_exp_rec x1 e3).

Definition close_exp_wrt_exp (x1:var) (e1 : exp 0) : exp 1 := close_exp_wrt_exp_rec x1 e1.

Lemma close_exp_wrt_exp_def : forall x e, close_exp_wrt_exp x e = close_exp_wrt_exp_rec x e.
Proof. auto. Qed.
Hint Rewrite close_exp_wrt_exp_def : close_exp_wrt_exp_rec.


(***********************************************************************)
(** * Substitution *)
(***********************************************************************)

(** Substitution replaces a free variable with a term.  The definition
    below is simple for two reasons:
      - Because bound variables are represented using indices, there
        is no need to worry about variable capture.
      - We assume that the term being substituted in is locally
        closed.  Thus, there is no need to shift indices when
        passing under a binder.
*)

(** 
    Note that [subst_exp] uses [x == y] for decidable equality.
    This operation is defined in the Metatheory library. 
    
    This definition is defined for *all* scoping levels of the term we are 
    substituting into. However, the replacement for y (i.e. the expression u)
    must be locally closed. As a result, we weaken it when we find it.

 *)

Equations subst_exp_rec {n} (u:exp n) (y:var) (e:exp n) : exp n :=
  subst_exp_rec u y (var_b m)   := var_b m;
  subst_exp_rec u y (var_f x)   := if x == y then u else var_f x;
  subst_exp_rec u y (abs e1)    :=  abs (subst_exp_rec (weaken_exp u) y e1);
  subst_exp_rec u y (app e1 e2) := app (subst_exp_rec u y e1) (subst_exp_rec u y e2).


Equations subst_exp (u : exp 0) (y :var) (e:exp 0) : exp 0 := 
  subst_exp u y e := subst_exp_rec u y e.

(*
Lemma subst_exp_var_f : forall u y x, 
    subst_exp u y (var_f x) = if x == y then u else var_f x.
Proof. intros. program_simpl. Qed.
Hint Rewrite subst_exp_var_f : subst_exp.
Lemma subst_exp_app : forall u y e1 e2, 
    subst_exp u y (app e1 e2) = app (subst_exp u y e1) (subst_exp u y e2).
Proof. intros. program_simpl. Qed.
Hint Rewrite subst_exp_app : subst_exp.
*)

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
    substitution for a bound variable, such as in the rule for beta
    reduction.  Note that only "dangling" indices (those that do not
    refer to any abstraction) can be opened.  Opening has no effect for
    terms that are locally closed.

    Natural numbers are just an inductive datatype with two constructors:
    [O] (as in the letter 'oh', not 'zero') and [S], defined in
    Coq.Init.Datatypes.  Coq allows literal natural numbers to be written
    using standard decimal notation, e.g., 0, 1, 2, etc.  The function
    [lt_eq_lt_dec] compares its two arguments for ordering.

    We do not assume that zero is the only unbound index in the term.
    Consequently, we must substract one when we encounter other unbound
    indices (i.e. the [inright] case).

    However, we do assume that the argument [u] is locally closed.  This
    assumption simplifies the implementation since we do not need to
    shift indices in [u] when passing under a binder. *)


Equations open_exp_wrt_exp_rec {k:nat} (u:exp k) (e:exp (S k)) : exp k :=
  open_exp_wrt_exp_rec u (var_b m) :=
     match decrease_fin k m with
        | Some f => var_b f
        | None => u
      end;
  open_exp_wrt_exp_rec u (var_f x)   := var_f x;
  open_exp_wrt_exp_rec u (abs e)     := abs (open_exp_wrt_exp_rec (weaken_exp u) e);
  open_exp_wrt_exp_rec u (app e1 e2) := app (open_exp_wrt_exp_rec u e1) (open_exp_wrt_exp_rec u e2).

(* Extraction open_exp_wrt_exp_rec. *)

Definition open_exp_wrt_exp (e : exp 1) (u : exp 0) : exp 0 := open_exp_wrt_exp_rec u e.

(***********************************************************************)
(** * Class + rewrite theory ??? *)
(***********************************************************************)

(* new! *)

Ltac simp_stlc := repeat first [ 
                       unfold open_exp_wrt_exp 
                     || unfold close_exp_wrt_exp 
                     || simp subst_exp
                     || simp open_exp_wrt_exp_rec 
                     || simp close_exp_wrt_exp_rec
                     || simp subst_exp_rec 
                     || simpl size_exp
                     || simp weaken_exp
                     || simpl fv_exp
                     || simp increase_fin 
                     || simp decrease_fin
                     ].


Class Syntax ( e : nat -> Set ) := {
    fv : e 0 -> vars ;
    size : e 0 -> nat ;
    weaken : forall n, e n -> e (S n) ;
    close : var -> e 0 -> e 1 ;
  }.

Class Subst (e : nat -> Set) (u : Set) := {
    open  : e 1 -> u -> e 0 ;
    subst : u -> var -> e 0 -> e 0 
}.

Instance Syntax_exp : Syntax exp := 
  { fv := fv_exp ; size := size_exp ; weaken := fun n => @weaken_exp n ; close := close_exp_wrt_exp }.
Instance Subst_exp_exp : Subst exp (exp 0) := 
  { open := open_exp_wrt_exp ; subst := subst_exp }.

(*
Lemma open_var_f : forall {x:atom}{u : exp 0}, open (var_f x) u = var_f x.
Proof. intros. program_simpl. Qed. 
Lemma open_app : forall {x:atom}{e1 e2}{u : exp 0}, open (app e1 e2) u = app (open e1 u) (open e2 u).
Proof. intros. program_simpl. Qed. 
*)

(***********************************************************************)
(** * Notations *)
(***********************************************************************)


(** Many common applications of opening replace index zero with an
    expression or variable.  The following definition provides a
    convenient shorthand for such uses.  Note that the order of
    arguments is switched relative to the definition above.  For
    example, [(open e x)] can be read as "substitute the variable [x]
    for index [0] in [e]" and "open [e] with the variable [x]."
*)

Declare Scope exp_scope.
Module StlcNotations.
Notation "[ z ~> u ] e" := (subst_exp_rec u z e) (at level 0) : exp_scope.
Notation "e ^ x"        := (open_exp_wrt_exp e (var_f x)) : exp_scope.
End StlcNotations.
Import StlcNotations.
Open Scope exp_scope.

(***********************************************************************)
(** * Local closure *)
(***********************************************************************)

(** Recall that [exp] admits terms that contain unbound indices.  We say
    that a term is locally closed when no indices appearing in it are
    unbound.  The proposition [lc_exp e] holds when an expression [e] is
    locally closed.

    The inductive definition below formalizes local closure such that the
    resulting induction principle serves as the structural induction
    principle over (locally closed) expressions.  In particular, unlike
    induction for type [exp], there are no cases for bound variables.
    Thus, the induction principle corresponds more closely to informal
    practice than the one arising from the definition of pre-terms.  *)

(*
Inductive lc_exp : exp -> Prop :=
 | lc_var_f : forall (x:var),
     lc_exp (var_f x)
 | lc_abs : forall (e:exp),
      (forall x , lc_exp (open e (var_f x)))  ->
     lc_exp (abs e)
 | lc_app : forall (e1 e2:exp),
     lc_exp e1 ->
     lc_exp e2 ->
     lc_exp (app e1 e2).
*)

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
 | typing_var : forall (G:ctx) (x:var) (T:typ),
     uniq G ->
     binds x T G  ->
     typing G (var_f x) T
 | typing_abs : forall (L:vars) (G:ctx) (T1:typ) (e:exp 1) (T2:typ),
     (forall x , x `notin` L -> typing ([(x,T1)] ++ G) (e ^ x) T2)  ->
     typing G (abs e) (typ_arrow T1 T2)
 | typing_app : forall (G:ctx) (e1 e2:exp 0) (T2 T1:typ),
     typing G e1 (typ_arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (app e1 e2) T2 .


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
     step (app  (abs e1) e2)  (open e1 e2)
 | step_app : forall (e1 e2 e1':exp 0),
     step e1 e1' ->
     step (app e1 e2) (app e1' e2).

#[global]
Hint Constructors typing step : core.
