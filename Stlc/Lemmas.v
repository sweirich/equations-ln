Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Program.
From Equations Require Import Equations Signature.
Require Import Coq.Classes.EquivDec.
Require Import Arith.
Close Scope program_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Import Lia.

Require Export Stlc.Definitions.




(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

#[global] Hint Resolve @plus_le_compat : lngen.

Ltac destruct_option :=
  let rec main x :=
    let h := fresh "EQ" in
    match type of x with
      | option _ => destruct x eqn:h
    end
  in
  match goal with
    | |- context [?x] => main x
    | H : _ |- _ => main H
    | _ : context [?x] |- _ => main x
  end.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= simp_stlc.


(* *********************************************************************** *)
(** * Theorems about [weaken] *)


Lemma size_exp_weaken_exp :
(forall n1 (e1 : exp n1),
  size_exp (weaken_exp e1) = size_exp e1).
Proof.
  intros n1 e1.
  funelim (weaken_exp e1); program_simpl.
Qed.

#[global] Hint Resolve size_exp_weaken_exp : lngen.
Hint Rewrite size_exp_weaken_exp using solve [auto] : lngen.  
Hint Rewrite size_exp_weaken_exp : weaken_exp.  

Lemma fv_exp_weaken_exp : 
(forall n1 (e1 : exp n1),
  fv_exp (weaken_exp e1) = fv_exp e1).
Proof. 
  intros n1 e1.
  funelim (weaken_exp e1); program_simpl.
Qed.

#[global] Hint Resolve fv_exp_weaken_exp : lngen.
Hint Rewrite fv_exp_weaken_exp using solve [auto] : lngen.  
Hint Rewrite fv_exp_weaken_exp : weaken_exp.  

(* *********************************************************************** *)
(** * Theorems about [size] *)

Lemma size_exp_min :
(forall n (e1 : exp n), 1 <= size_exp e1).
Proof.
  intros n e1.  dependent induction e1; default_simp.  
Admitted. (* lia ??? *)

#[global] Hint Resolve size_exp_min : lngen.

Lemma size_exp_close_exp_wrt_exp :
(forall n1 (e1 : exp n1) x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1).
Proof.
intros n1 e1 x1.  
funelim (close_exp_wrt_exp x1 e1); default_simp. 
Qed.

#[global] Hint Resolve size_exp_close_exp_wrt_exp : lngen.

Lemma size_exp_open_exp_wrt_exp :
(forall k (e1 : exp (S k)) (e2 : exp k),
  size_exp e1 <= size_exp (open_exp_wrt_exp e2 e1)).
Proof.
intros k e1 e2.
funelim (open_exp_wrt_exp e2 e1); default_simp; try lia; eauto with lngen.
Admitted.

Lemma size_exp_open_exp_wrt_exp_var :
(forall k (e : exp (S k)) x,
  size_exp (open_exp_wrt_exp (var_f x) e) = size_exp e).
Proof.
intros k e x.
dependent induction e; default_simp. destruct_option; default_simp.
Qed.

#[global] Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.

(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= simp_stlc.

Ltac noconf_exp := 
  match goal with 
    | [ H : var_b _ = var_b _ |- _ ] => noconf H
    | [ H : var_f _ = var_f _ |- _ ] => noconf H
    | [ H : abs _ = abs _ |- _ ] => noconf H
    | [ H : app _ _ = app _ _ |- _ ] => noconf H
  end.

Lemma close_exp_wrt_exp_inj :
(forall k (e1 : exp k) e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2).
Proof.
  intros k e1 e2 x1.
  funelim (close_exp_wrt_exp x1 e1).
  all: default_simp.
  all: match goal with
          | |- _ = ?term => destruct term
        end.
  all: try simp close_exp_wrt_exp in H.
  all: try noconf_exp.
  all: try discriminate.
  all: try simp close_exp_wrt_exp in *.
  all: try (destruct (x1 == x); simpl in H; try discriminate).
  all: try noconf_exp; default_simp.
  + eapply increase_fin_inj; eauto.  
  + exfalso. eapply increase_not_n; eauto.
  + exfalso. eapply increase_not_n; eauto.  
Qed.

Hint Immediate close_exp_wrt_exp_inj : lngen.

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
(forall n1 (e1 : exp (S n1)) x1 ,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp (var_f x1) e1) = e1).
Proof.
intros. 
dependent induction e1.
all: simp_stlc.
all: default_simp.
destruct decrease_fin eqn:EQ; default_simp. 
eauto using decrease_increase_fin.
eauto using decrease_to_fin.
Qed.

#[global] Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen. 


Lemma open_exp_wrt_exp_close_exp_wrt_exp :
(forall n1 (e1 : exp n1) x1,
  open_exp_wrt_exp (var_f x1) (close_exp_wrt_exp x1 e1) = e1).
Proof.
  intros n1 e1. dependent induction e1; default_simp.
Qed.

#[global] Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.


Lemma open_exp_wrt_exp_inj :
(forall n1 (e2 e1:exp (S n1)) x1,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp (var_f x1) e2 = open_exp_wrt_exp (var_f x1) e1 ->
  e2 = e1).
Proof.
 intros k e2 e1 x1 FV1 FV2. 
 remember (var_f x1) as u.
 funelim (open_exp_wrt_exp u e2). 
 all: simp open_exp_wrt_exp.
 all: intros h.
 all: match goal with [ |- _ = ?e ] => dependent elimination e end.
 all: simp open_exp_wrt_exp in h.
 all: noconf h.
 all: try destruct_option. 
 all: try destruct_option. 
 all: try noconf h.
 all: simpl in FV1; simpl in FV2.
 all: default_simp. 
 all: try (rewrite <- EQ0 in EQ; apply decrease_fin_inj in EQ).
 all: eauto.
Qed.

Hint Immediate open_exp_wrt_exp_inj : lngen.

(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= simp_stlc.

Lemma close_exp_wrt_exp_weaken_exp :
(forall n1 (e1 : exp n1) x1,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp x1 e1 = weaken_exp e1).
Proof.
intros.
dependent induction e1; default_simp.
Qed.

#[global] Hint Resolve close_exp_wrt_exp_weaken_exp : lngen.
Hint Rewrite close_exp_wrt_exp_weaken_exp using solve [auto] : lngen.

Lemma open_exp_wrt_exp_weaken_exp :
forall n1 (e2 : exp n1) e1,
  open_exp_wrt_exp e1 (weaken_exp e2) = e2.
Proof.
intros n1 e2.
funelim (weaken_exp e2); default_simp.
Qed.
#[global] Hint Resolve open_exp_wrt_exp_weaken_exp : lngen.
Hint Rewrite open_exp_wrt_exp_weaken_exp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen; simp_stlc.

Lemma fv_exp_close_exp_wrt_exp :
(forall n1 (e1 : exp n1) x1,
  fv_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (fv_exp e1)).
Proof.
dependent induction e1; default_simp; fsetdec. 
Qed.

#[global] Hint Resolve fv_exp_close_exp_wrt_exp : lngen.
Hint Rewrite fv_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma fv_exp_open_exp_wrt_exp_lower :
(forall n1 (e1 : exp (S n1)) (e2 : exp n1),
  fv_exp e1 [<=] fv_exp (open_exp_wrt_exp e2 e1)).
Proof.
  intros n1 e1 e2.
  funelim  (open_exp_wrt_exp e2 e1); 
    simp_stlc;
    try destruct (decrease_fin k f); 
    default_simp; fsetdec.
Qed.

#[global] Hint Resolve fv_exp_open_exp_wrt_exp_lower : lngen.

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_upper :
(forall n1 (e1 : exp (S n1)) (e2 : exp n1),
  fv_exp (open_exp_wrt_exp e2 e1) [<=] fv_exp e2 `union` fv_exp e1).
Proof.
  intros n1 e1 e2.
  funelim (open_exp_wrt_exp e2 e1); simp_stlc. 
  all: try destruct decrease_fin; default_simp. 
  simp lngen in H.
Qed.

#[global] Hint Resolve fv_exp_open_exp_wrt_exp_upper : lngen.

Lemma fv_exp_subst_exp_wrt_exp_fresh :
(forall n1 (e1 : exp n1) e2 x1,
  x1 `notin` fv_exp e1 ->
  fv_exp (subst_exp_wrt_exp e2 x1 e1) [=] fv_exp e1).
Proof.
intros n1 e1.
dependent induction e1; default_simp.
Qed.

#[global] Hint Resolve fv_exp_subst_exp_wrt_exp_fresh : lngen.
Hint Rewrite fv_exp_subst_exp_wrt_exp_fresh using solve [auto] : lngen.

Lemma fv_exp_subst_exp_wrt_exp_lower :
(forall n1 (e1 : exp n1) e2 x1,
  remove x1 (fv_exp e1) [<=] fv_exp (subst_exp_wrt_exp e2 x1 e1)).
Proof.
intros n1 e1.
dependent induction e1; default_simp.
fsetdec.
Qed.

#[global] Hint Resolve fv_exp_subst_exp_wrt_exp_lower : lngen.

(* begin hide *)

Lemma fv_exp_subst_exp_wrt_exp_notin :
(forall n1 (e1 : exp n1) e2 x1 x2,
  x2 `notin` fv_exp e1 ->
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp (subst_exp_wrt_exp e2 x1 e1)).
Proof.
intros n1 e1.
dependent induction e1; default_simp.
eapply IHe1. auto. simp_stlc.
Qed.

#[global] Hint Resolve fv_exp_subst_exp_wrt_exp_notin : lngen.

Lemma fv_exp_subst_exp_wrt_exp_upper :
(forall n1 (e1 : exp n1) e2 x1,
  fv_exp (subst_exp_wrt_exp e2 x1 e1) [<=] fv_exp e2 `union` remove x1 (fv_exp e1)).
Proof.
intros n1 e1.
dependent induction e1; default_simp.
fsetdec.
specialize (IHe1 (weaken_exp e2)).
simp weaken_exp in IHe1.
Qed.

#[global] Hint Resolve fv_exp_subst_exp_wrt_exp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= simp_stlc; autorewrite with lngen.

Lemma subst_exp_close_exp_wrt_exp :
forall n1 (e2 : exp n1) (e1 : exp n1) x1 x2,
  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  subst_exp_wrt_exp (weaken_exp e1) x1 (close_exp_wrt_exp x2 e2) =
        close_exp_wrt_exp x2 (subst_exp_wrt_exp e1 x1 e2).
Proof.
intros n1 e2.
dependent induction e2. 
all: default_simp.
specialize (IHe2 (weaken_exp e1)).
eapply IHe2; simp_stlc; auto.
Qed.


#[global] Hint Resolve subst_exp_close_exp_wrt_exp : lngen.


Lemma subst_exp_wrt_exp_fresh_eq :
forall n1 (e2 : exp n1) e1 x1,
  x1 `notin` fv_exp e2 ->
  subst_exp_wrt_exp e1 x1 e2 = e2.
Proof.
  intros. 
  dependent induction e2; default_simp.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_fresh_eq : lngen.
Hint Rewrite subst_exp_wrt_exp_fresh_eq using solve [auto] : lngen.

Lemma subst_exp_wrt_exp_fresh_same :
(forall n1 (e2 : exp n1) e1 x1,
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (subst_exp_wrt_exp e1 x1 e2)).
Proof.
intros n1 e2.
dependent induction e2; default_simp.
specialize (IHe2 (weaken_exp e1)).
eapply IHe2. simp_stlc.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_fresh_same : lngen.

Lemma subst_exp_wrt_exp_fresh :
(forall n1 (e2:exp n1) e1 x1 x2,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (subst_exp_wrt_exp e1 x2 e2)).
Proof.
intros n1 e2.
dependent induction e2; default_simp.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_fresh : lngen.

Lemma subst_exp_wrt_exp_weaken_exp : 
  forall n (e1 : exp n) x1 u,
    weaken_exp (subst_exp_wrt_exp e1 x1 u) = 
    subst_exp_wrt_exp (weaken_exp e1) x1 (weaken_exp u).
Proof.
  intros.
  funelim (weaken_exp u); simp_stlc; default_simp.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_weaken_exp : lngen.
Hint Rewrite subst_exp_wrt_exp_weaken_exp : lngen.

(* SCW: this one might be simpler if we only substitute 
   locally closed terms *)
Lemma subst_exp_open_exp_wrt_exp :
(forall n1 (e1 : exp n1) e2 (e3 : exp (S n1)) x1,
  subst_exp_wrt_exp e1 x1 (open_exp_wrt_exp e2 e3) =
    open_exp_wrt_exp (subst_exp_wrt_exp e1 x1 e2) 
                         (subst_exp_wrt_exp (weaken_exp e1) x1 e3)).
Proof.
intros n1 e1 e2 e3 x1.
funelim (open_exp_wrt_exp e2 e3).
all: default_simp.
destruct (decrease_fin k f) eqn:E1.
default_simp.
default_simp.
Qed.

#[global] Hint Resolve subst_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_open_exp_wrt_exp_var :
forall n1 (e2 : exp (S n1)) e1 x1 x2,
  x1 <> x2 ->
  open_exp_wrt_exp (var_f x2) (subst_exp_wrt_exp (weaken_exp e1) x1 e2) = 
    subst_exp_wrt_exp e1 x1 (open_exp_wrt_exp (var_f x2) e2).
Proof.
intros; default_simp.
Admitted.

#[global] Hint Resolve subst_exp_open_exp_wrt_exp_var : lngen.

(* begin hide *)

Lemma subst_exp_wrt_exp_spec :
(forall n (e1 e2 : exp n) x1,
  subst_exp_wrt_exp e2 x1 e1 = open_exp_wrt_exp e2 (close_exp_wrt_exp  x1 e1)).
Proof.
intros n e1 e2 x1.
dependent induction e1.
all: default_simp.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_spec : lngen.

(* begin hide *)

Lemma subst_exp_wrt_exp_subst_exp_wrt_exp :
(forall n (e1 e2 e3 : exp n) x2 x1,
  x2 `notin` fv_exp e2 ->
  x2 <> x1 ->
  subst_exp_wrt_exp e2 x1 (subst_exp_wrt_exp e3 x2 e1) = 
    subst_exp_wrt_exp (subst_exp_wrt_exp e2 x1 e3) x2 (subst_exp_wrt_exp e2 x1 e1)).
Proof.
intros n e1.
dependent induction e1; intros.
all: default_simp.
rewrite IHe1; 
default_simp.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_subst_exp_wrt_exp : lngen.

Lemma subst_exp_wrt_exp_close_exp_wrt_exp_open_exp_wrt_exp :
(forall n1 (e2 : exp (S n1)) e1 x1 x2,
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  subst_exp_wrt_exp (weaken_exp e1) x1 e2 = 
    close_exp_wrt_exp x2 
       (subst_exp_wrt_exp e1 x1 (open_exp_wrt_exp (var_f x2) e2))).
Proof.
intros n e2.
dependent induction e2; intros.
all: default_simp.
all: try destruct (decrease_fin n f) eqn:E.
all: default_simp.
symmetry. eauto using decrease_increase_fin.
symmetry. eauto using decrease_to_fin.
specialize (IHe2 _ e2 ltac:(auto) ltac:(auto)).
specialize (IHe2 (weaken_exp e1)).
eapply IHe2; eauto.
all: simp_stlc. 
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_wrt_exp_abs :
forall x2 (e2 : exp 1) (e1 : exp 0) x1,
  x2 `notin` fv_exp e1 `union` fv_exp e2 `union` singleton x1 ->
  subst_exp_wrt_exp e1 x1 (abs e2) = 
    abs (close_exp_wrt_exp x2 (subst_exp_wrt_exp e1 x1 (open_exp_wrt_exp (var_f x2) e2))).
Proof.
default_simp. 
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_abs : lngen.

Lemma subst_exp_wrt_exp_intro :
forall n1 (e1 : exp (S n1)) x1 e2,
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp e2 e1 = subst_exp_wrt_exp e2 x1 (open_exp_wrt_exp (var_f x1) e1).
Proof.
dependent induction e1; default_simp.
all: try destruct decrease_fin eqn:E.
all: default_simp.
Qed.

#[global] Hint Resolve subst_exp_wrt_exp_intro : lngen.
Hint Rewrite subst_exp_wrt_exp_intro using solve [auto] : lngen.

(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.


Instance STE :  SyntaxTheory exp := {
  size_weaken := size_exp_weaken_exp;
  fv_weaken := fv_exp_weaken_exp;
  size_min  := size_exp_min;
  subst_intro := subst_exp_wrt_exp_intro;
  subst_open_var := subst_exp_open_exp_wrt_exp_var 
}.

Opaque Syntax_exp.
