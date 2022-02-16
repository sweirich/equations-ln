(***********************************************************************)
(** * Definition of STLC *)
(***********************************************************************)

(** This file containes all of the definitions for a locally-nameless
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

(*  the line above produces the definition

typ_eq_dec
     : forall x y : typ, {x = y} + {x <> y}
*)

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

(* The size of an expression *)
Fixpoint size_exp {n} (e1 : exp n) : nat :=
  match e1 with
    | abs e2 => 1 + (size_exp e2)
    | var_f x1 => 1
    | var_b m => 1
    | app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
  end.

(* Weaken the number of binders allowed in an expression by 1 *)
Equations weaken_exp {n} (e : exp n): exp (S n):= {
  weaken_exp  (var_b m) => var_b (increase_fin m);
  weaken_exp  (var_f x) => var_f x;
  weaken_exp  (abs t)   => abs (weaken_exp t);
  weaken_exp  (app f t) => app (weaken_exp f) (weaken_exp t)
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

Equations subst_exp_wrt_exp {n} (u:exp n) (y:var) (e:exp n) : exp n :=
  subst_exp_wrt_exp u y (var_b m)   := var_b m;
  subst_exp_wrt_exp u y (var_f x)   := if x == y then u else var_f x;
  subst_exp_wrt_exp u y (abs e1)    := abs (subst_exp_wrt_exp (weaken_exp u) y e1);
  subst_exp_wrt_exp u y (app e1 e2) := app (subst_exp_wrt_exp u y e1) (subst_exp_wrt_exp u y e2).

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


Equations open_exp_wrt_exp {k:nat} (u:exp k) (e:exp (S k)) : exp k :=
  open_exp_wrt_exp u (var_b m) :=
     match decrease_fin k m with
        | Some f => var_b f
        | None => u
      end;
  open_exp_wrt_exp u (var_f x)   := var_f x;
  open_exp_wrt_exp u (abs e)     := abs (open_exp_wrt_exp (weaken_exp u) e);
  open_exp_wrt_exp u (app e1 e2) := app (open_exp_wrt_exp u e1) (open_exp_wrt_exp u e2).


(***********************************************************************)
(** * Class + rewrite theory ??? *)
(***********************************************************************)

(* new! *)

Ltac simp_stlc := repeat first [ 
                       simp subst_exp_wrt_exp
                     || simp open_exp_wrt_exp
                     || simp close_exp_wrt_exp
                     || simp weaken_exp
                     || simpl size_exp
                     || simpl fv_exp
                     || simp increase_fin 
                     || simp decrease_fin
                     ].

(* single parameter for now *)


Instance Syntax_exp : Syntax exp := { 
    evar := fun n => @var_f n;

    fv := fun n => @fv_exp n;
    size := fun {n} => @size_exp n; 
    weaken := fun {n} =>  @weaken_exp n;
    close := fun {n} => @close_exp_wrt_exp n;
    open := fun {n} => @open_exp_wrt_exp n;
    subst := fun {n} => @subst_exp_wrt_exp n}.
Opaque Syntax_exp.

Example test : forall (e : exp 0), size e = 1.
intros e.
simpl. (* not sufficient *)
cbn. (* not sufficent *)
program_simpl.
simp size_exp.
Abort.

Lemma fv_exp_var_b : forall n (m: fin n), fv (var_b m) = {}. 
Proof. reflexivity. Qed.
Lemma fv_exp_var_f : forall n (x:atom), fv (evar (n:=n) x) = {{x}}.
Proof. reflexivity. Qed.
Lemma fv_exp_abs : forall n (e: exp (S n)), fv (abs e) = fv e.
Proof. reflexivity. Qed.
Lemma fv_exp_app : forall n (e1 : exp n) (e2: exp n), fv (app e1 e2) = fv e1 `union` fv e2.
Proof. reflexivity. Qed.

Hint Rewrite fv_exp_var_b fv_exp_var_f fv_exp_abs fv_exp_app : fv.

(* Re-define behavior of size in terms of size_exp *)
Lemma size_exp_var_b : forall n (m: fin n), size (var_b m) = 1. 
Proof. reflexivity. Qed.
Lemma size_exp_var_f : forall n (x:atom), size (evar (n:=n) x) = 1.
Proof. reflexivity. Qed.
Lemma size_exp_abs : forall n (e: exp (S n)), size (abs e) = 1 + (size e).
Proof. reflexivity. Qed.
Lemma size_exp_app : forall n (e1 : exp n) (e2: exp n), size (app e1 e2) = 1 + size e1 + size e2.
Proof. reflexivity. Qed.

Hint Rewrite size_exp_var_b size_exp_var_f size_exp_abs size_exp_app : size.

Lemma weaken_exp_var_b : forall n (m: fin n),   weaken  (var_b m) = var_b (increase_fin m).
Proof. reflexivity. Qed.
Lemma weaken_exp_var_f : forall n (x:atom), weaken (evar (n:=n) x) = evar x.
Proof. reflexivity. Qed.
Lemma weaken_exp_abs : forall n (e: exp (S n)), weaken (abs e) = abs (weaken e).
Proof. reflexivity. Qed.
Lemma weaken_exp_app : forall n (e1 : exp n) (e2: exp n), weaken (app e1 e2) = app (weaken e1) (weaken e2).
Proof. reflexivity. Qed.

Hint Rewrite weaken_exp_var_b weaken_exp_var_f weaken_exp_abs weaken_exp_app : weaken.

Lemma open_exp_var_b : forall n (u:exp n) (m: fin (S n)), open u (var_b m) = 
match decrease_fin n m with
        | Some f => var_b f
        | None => u
      end.
Proof. reflexivity. Qed.
Lemma open_exp_var_f : forall n (u:exp n) (x:atom), open u (evar (n:= S n) x) = evar x.
Proof. reflexivity. Qed.

Lemma open_exp_abs : forall n (u:exp n) (e: exp (S (S n))), 
    open u (abs e) = abs (open (weaken u) e).
Proof. reflexivity. Qed. 
Lemma open_exp_app : forall n (u:exp n) (e1 : exp (S n)) (e2: exp (S n)), 
    open u (app e1 e2) = app (open u e1) (open u e2).
Proof. reflexivity. Qed.

Hint Rewrite open_exp_var_b open_exp_var_f open_exp_abs open_exp_app : open.

Lemma subst_exp_var_b : forall n (u:exp n) (y:atom) (m: fin n), 
    subst u y (var_b m) = var_b m.
Proof. reflexivity. Qed.
Lemma subst_exp_var_f : forall n (u:exp n) (y:atom) (x:atom), 
    subst u y (evar (n:=n) x) = if x == y then u else evar x.
Proof. reflexivity. Qed.
Lemma subst_exp_abs : forall n (u:exp n) (y:atom) (e: exp (S n)), 
    subst u y (abs e) = abs (subst (weaken u) y e).
Proof. reflexivity. Qed.
Lemma subst_exp_app : forall n (u:exp n) (y:atom) (e1 : exp n) (e2: exp n), 
    subst u y (app e1 e2) = app (subst u y e1) (subst u y e2).
Proof. reflexivity. Qed.

Hint Rewrite subst_exp_var_b subst_exp_var_f subst_exp_abs subst_exp_app : subst.






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
     step (app (abs e1) e2) (open e2 e1)
 | step_app : forall (e1 e2 e1':exp 0),
     step e1 e1' ->
     step (app e1 e2) (app e1' e2).


#[global]
Hint Constructors typing step : core.
