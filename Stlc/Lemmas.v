From Coq Require Import ssreflect ssrfun ssrbool.

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

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)

(* begin hide *)

(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

(*
Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 =>
  typ_ind' H1 H2 H3.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 =>
  typ_rec' H1 H2 H3.

Scheme exp_ind' := Induction for exp Sort Prop.

Definition exp_mutind :=
  fun H1 H2 H3 H4 H5 =>
  exp_ind' H1 H2 H3 H4 H5.

Scheme exp_rec' := Induction for exp Sort Set.

Definition exp_mutrec :=
  fun H1 H2 H3 H4 H5 =>
  exp_rec' H1 H2 H3 H4 H5.
*)

(* end hide *)

(* *********************************************************************** *)
(** * Close *)


(* *********************************************************************** *)
(** * Degree *)

(* subsumed by the indexed representation. *)

(*
(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_exp_wrt_exp {n} : nat -> exp n -> Prop :=
  | degree_wrt_exp_abs : forall n1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (abs e1)
  | degree_wrt_exp_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (var_f x1)
  | degree_wrt_exp_var_b : forall n1 n2,
      forall pf, lt n2 n1 ->
    degree_exp_wrt_exp n1 (var_b pf)
  | degree_wrt_exp_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (app e1 e2).

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Definition degree_exp_wrt_exp_mutind :=
  fun H1 H2 H3 H4 H5 =>
  degree_exp_wrt_exp_ind' H1 H2 H3 H4 H5.

#[global] Hint Constructors degree_exp_wrt_exp : core lngen.
*)

(* begin hide *)

(* *********************************************************************** *)
(** * Local closure (induction principles) *)
(*

Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Definition lc_exp_mutind :=
  fun H1 H2 H3 H4 =>
  lc_exp_ind' H1 H2 H3 H4.

#[global] Hint Constructors lc_exp : core lngen.
*)
(* end hide *)


(* *********************************************************************** *)
(** * Body *)

(*
Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (var_f x1)).

#[global] Hint Unfold body_exp_wrt_exp.
*)

(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

#[global] Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)


Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


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

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.


(* begin hide *)

(*
Lemma size_typ_min_mutual :
(forall T1, 1 <= size_typ T1).
Proof.
intros T1. induction T1; default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall T1, 1 <= size_typ T1.
Proof.
pose proof size_typ_min_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve size_typ_min : lngen.
*)

(* begin hide *)

Lemma size_exp_min_mutual :
(forall {n} (e1 : exp n), 1 <= size_exp e1).
Proof.
  move=>n e1.  dependent induction e1; default_simp.  
Admitted. (* lia ??? *)

(* end hide *)

Lemma size_exp_min :
forall {n} (e1:exp n), 1 <= size_exp e1.
Proof.
move=>n.
pose proof (@size_exp_min_mutual n) as H; intuition eauto.
Qed.

#[global] Hint Resolve size_exp_min : lngen.

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec_mutual :
(forall {n1} (e1 : exp n1) x1,
  size_exp (close_exp_wrt_exp_rec x1 e1) = size_exp e1).
Proof.
move=> n1 e1 x1.  
funelim (close_exp_wrt_exp_rec x1 e1); program_simpl; simp close_exp_wrt_exp_rec. 
default_simp. 
Qed.


(* end hide *)

Lemma size_exp_open_exp_wrt_exp_rec_mutual :
(forall k (e1 : exp (S k)) (e2 : exp k),
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec e2 e1)).
Proof.
intros k e1 e2.
apply_funelim (open_exp_wrt_exp_rec e2 e1); default_simp; try lia; eauto with lngen.
Admitted.

Lemma size_exp_open_exp_wrt_exp_rec :
forall k (e1 : exp (S k)) (e2 : exp k),
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec e2 e1).
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve size_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma size_exp_open_exp_wrt_exp :
forall e1 e2,
  size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp. 
Qed.

#[global] Hint Resolve size_exp_open_exp_wrt_exp : lngen.


Lemma size_exp_open_exp_wrt_exp_rec_var_mutual :
(forall k ( e1 : exp (S k)) x1,
  size_exp (open_exp_wrt_exp_rec (var_f x1) e1) = size_exp e1).
Proof.
intros k e1 x1.
dependent induction e1; simp_stlc; default_simp.
destruct decrease_fin; default_simp.
Qed.

Lemma size_exp_open_exp_wrt_exp_rec_var :
forall k (e1 : exp (S k)) x1 ,
  size_exp (open_exp_wrt_exp_rec (var_f x1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.
#[global] Hint Resolve size_exp_open_exp_wrt_exp_rec_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_exp_open_exp_wrt_exp_var :
forall (e1 : exp 1) x1,
  size_exp (open_exp_wrt_exp e1 (var_f x1)) = size_exp e1.
Proof.
  simp_stlc; default_simp. 
Qed.

#[global] Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.

(* *********************************************************************** *)
(** * Theorems about [degree] *)
(*
Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_exp_wrt_exp_S_mutual :
(forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_S :
forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_S_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve degree_exp_wrt_exp_S : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[global] Hint Resolve degree_exp_wrt_exp_O : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[global] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp :
forall e1 e2,
  degree_exp_wrt_exp 1 e1 ->
  degree_exp_wrt_exp 0 e2 ->
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[global] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_inv :
forall e1 e2,
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_exp 1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_inv : lngen.
*)


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj_mutual :
(forall k (e1 : exp k) e2 x1,
  close_exp_wrt_exp_rec x1 e1 = close_exp_wrt_exp_rec x1 e2 ->
  e1 = e2).
Proof.
  intros k e1 e2 x1.
  funelim (close_exp_wrt_exp_rec x1 e1).
  all: program_simpl.
  all: match goal with
          | |- _ = ?term => destruct term
        end;
     simp close_exp_wrt_exp_rec in H;
     noconf H.
  all: try discriminate.
  all: try simp close_exp_wrt_exp_rec in *.
  all: try (destruct (x1 == x); simpl in H; try discriminate).
  + apply increase_fin_inj in H. rewrite H. auto.
  + noconf H. symmetry in H.
    move: (increase_not_n f) => h. done.
  + noconf H. move: (increase_not_n f) => h. done.
  + destruct (x1 == x0); subst; simpl in H; try discriminate; auto.
  + destruct (x1 == x0); subst; simpl in H; try discriminate; auto.
    noconf H. auto.
  + noconf H0. f_equal. eapply H. auto.
  + noconf H1. f_equal. eapply H. eauto. eapply H0. eauto.
Qed.

Lemma close_exp_wrt_exp_rec_inj :
forall k (e1 e2 : exp k) x1,
  close_exp_wrt_exp_rec x1 e1 = close_exp_wrt_exp_rec x1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma close_exp_wrt_exp_inj :
forall (e1 e2 : exp 0) x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate close_exp_wrt_exp_inj : lngen.

(* begin hide *)


Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall {n1} (e1 : exp (S n1)) x1 ,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp_rec x1 (open_exp_wrt_exp_rec (var_f x1) e1) = e1).
Proof.
intros. 
dependent induction e1.
all: simp open_exp_wrt_exp_rec.
all: simp close_exp_wrt_exp_rec.
+ destruct (decrease_fin n1 f) eqn:E1.
  ++ simp close_exp_wrt_exp_rec. f_equal.
  eauto using decrease_increase_fin.
  ++ simp weaken. simp close_exp_wrt_exp_rec.
     rewrite eq_dec_refl. simpl.
     f_equal. eauto using decrease_to_fin.
+ destruct (x1 == x); subst; simpl. simpl in H. fsetdec. auto.
+ f_equal.
  rewrite IHe1; eauto.
+ simpl in H. f_equal. rewrite IHe1_1; eauto. rewrite IHe1_2; eauto.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall {n1} (e1:exp (S n1)) x1,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp_rec x1 (open_exp_wrt_exp_rec (var_f x1) e1) = e1.
Proof.
intro n1.
pose proof (@close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual n1) as H; intuition eauto.
Qed.

#[global] Hint Resolve close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.
(* Hint Rewrite close_exp_wrt_exp_rec_open_exp_wrt_exp_rec using solve [auto] : lngen. *)

(* end hide *)

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
forall (e1 : exp 1) x1,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp e1 (var_f x1)) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[global] Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual :
(forall n1 (e1 : exp n1) x1,
  open_exp_wrt_exp_rec (var_f x1) (close_exp_wrt_exp_rec x1 e1) = e1).
Proof.
intros.
dependent induction e1; simp close_exp_wrt_exp_rec.
+ funelim (increase_fin f); simp_stlc; default_simp.
+ default_simp. simp_stlc. default_simp.
+ simp_stlc. default_simp.
+ simp_stlc. default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec :
forall n1 (e1 : exp n1) x1,
  open_exp_wrt_exp_rec (var_f x1) (close_exp_wrt_exp_rec x1 e1) = e1.
Proof.
pose proof open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve open_exp_wrt_exp_rec_close_exp_wrt_exp_rec : lngen.
Hint Rewrite open_exp_wrt_exp_rec_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_exp_wrt_exp (close_exp_wrt_exp x1 e1) (var_f x1) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[global] Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj_mutual :
(forall n1 (e2 e1:exp (S n1)) x1,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp_rec (var_f x1) e2 = open_exp_wrt_exp_rec (var_f x1) e1 ->
  e2 = e1).
Proof.
 intros k e1 e2 x1 FV1 FV2. 
 remember (var_f x1) as u.
 funelim (open_exp_wrt_exp_rec u e1). 
 all: simp open_exp_wrt_exp_rec.
 all: intros h.
 all: match goal with [ |- _ = ?e ] => dependent elimination e end.
 all: simp open_exp_wrt_exp_rec in h.
 all: noconf h.
 all: try destruct (decrease_fin k f) eqn:E1.
 all: try destruct (decrease_fin k f0) eqn:E2.
 all: try noconf h.
 all: simpl in FV1; simpl in FV2.
 all: try solve [f_equal; eauto].
 all: try (rewrite <- E2 in E1; apply decrease_fin_inj in E1; f_equal; auto).
 all: fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj :
forall n1 (e2 e1 : exp (S n1)) x1,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp_rec (var_f x1) e2 = open_exp_wrt_exp_rec (var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma open_exp_wrt_exp_inj :
forall e2 e1 x1,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp e2 (var_f x1) = open_exp_wrt_exp e1 (var_f x1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate open_exp_wrt_exp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

(*
Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1.
Proof.
pose proof degree_exp_wrt_exp_of_lc_exp_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve degree_exp_wrt_exp_of_lc_exp : lngen.

(* begin hide *)

Lemma lc_exp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_degree :
forall e1,
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1.
Proof.
intros e1; intros;
pose proof (lc_exp_of_degree_size_mutual (size_exp e1));
intuition eauto.
Qed.

#[global] Hint Resolve lc_exp_of_degree : lngen.

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_exp_of_lc_exp in J1; clear H
          end).

Lemma lc_abs_exists :
forall x1 e1,
  lc_exp (open_exp_wrt_exp e1 (var_f x1)) ->
  lc_exp (abs e1).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_exp (abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_abs_exists x1).

Lemma lc_body_exp_wrt_exp :
forall e1 e2,
  body_exp_wrt_exp e1 ->
  lc_exp e2 ->
  lc_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold body_exp_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
exp_lc_exists_tac;
eauto with lngen.
Qed.

#[global] Hint Resolve lc_body_exp_wrt_exp : lngen.

Lemma lc_body_abs_1 :
forall e1,
  lc_exp (abs e1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

#[global] Hint Resolve lc_body_abs_1 : lngen.
*)

(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall n1 (e1 : exp n1) x1,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp_rec x1 e1 = weaken_exp e1).
Proof.
intros.
dependent induction e1; simp_stlc; default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall n1 (e1 : exp n1) x1,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp_rec x1 e1 = weaken_exp e1.
Proof.
pose proof close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve close_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma close_exp_wrt_exp_lc_exp :
forall (e1 : exp 0) x1,
  x1 `notin` fv_exp e1 ->
  close_exp_wrt_exp x1 e1 = weaken_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[global] Hint Resolve close_exp_wrt_exp_lc_exp : lngen.
Hint Rewrite close_exp_wrt_exp_lc_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_exp_wrt_exp_rec_weaken_exp_mutual :
forall n1 (e2 : exp n1) e1,
  open_exp_wrt_exp_rec e1 (weaken_exp e2) = e2.
Proof.
intros n1 e2 e1.
funelim (weaken_exp e2).
all: simp_stlc; default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall n1 (e2 : exp n1) e1,
  open_exp_wrt_exp_rec e1 (weaken_exp e2) = e2.
Proof.
pose proof open_exp_wrt_exp_rec_weaken_exp_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve open_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma open_exp_wrt_exp_lc_exp :
forall e2 e1,
  open_exp_wrt_exp (weaken_exp e2) e1 = e2.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[global] Hint Resolve open_exp_wrt_exp_lc_exp : lngen.
Hint Rewrite open_exp_wrt_exp_lc_exp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_exp_close_exp_wrt_exp_rec_mutual :
(forall n1 (e1 : exp n1) x1,
  fv_exp (close_exp_wrt_exp_rec x1 e1) [=] remove x1 (fv_exp e1)).
Proof.
dependent induction e1; intros;
simp_stlc;
default_simp; fsetdec. 
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_close_exp_wrt_exp_rec :
forall n1 (e1 : exp n1) x1,
  fv_exp (close_exp_wrt_exp_rec x1 e1) [=] remove x1 (fv_exp e1).
Proof.
pose proof fv_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve fv_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite fv_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_exp_close_exp_wrt_exp :
forall e1 x1,
  fv_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (fv_exp e1).
Proof.
  simp_stlc; default_simp.
Qed.

#[global] Hint Resolve fv_exp_close_exp_wrt_exp : lngen.
Hint Rewrite fv_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall n1 (e1 : exp (S n1)) (e2 : exp n1),
  fv_exp e1 [<=] fv_exp (open_exp_wrt_exp_rec e2 e1)).
Proof.
  intros n1 e1 e2.
  funelim  (open_exp_wrt_exp_rec e2 e1); 
    simp_stlc;
    try destruct (decrease_fin k f); 
    default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_lower :
forall n1 (e1 : exp (S n1)) (e2 : exp n1),
  fv_exp e1 [<=] fv_exp (open_exp_wrt_exp_rec e2 e1).
Proof.
pose proof fv_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve fv_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

Lemma fv_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fv_exp e1 [<=] fv_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[global] Hint Resolve fv_exp_open_exp_wrt_exp_lower : lngen.

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall n1 (e1 : exp (S n1)) (e2 : exp n1),
  fv_exp (open_exp_wrt_exp_rec e2 e1) [<=] fv_exp e2 `union` fv_exp e1).
Proof.
  intros n1 e1 e2.
  funelim (open_exp_wrt_exp_rec e2 e1); simp_stlc. 
  all: try destruct decrease_fin; default_simp. 
  move:H. simp_stlc. 
Qed.
(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_upper :
forall n (e1 : exp (S n)) (e2 : exp n),
  fv_exp (open_exp_wrt_exp_rec e2 e1) [<=] fv_exp e2 `union` fv_exp e1.
Proof.
pose proof fv_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve fv_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

Lemma fv_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fv_exp (open_exp_wrt_exp e1 e2) [<=] fv_exp e2 `union` fv_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[global] Hint Resolve fv_exp_open_exp_wrt_exp_upper : lngen.

(* begin hide *)

Lemma fv_exp_subst_exp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fv_exp e1 ->
  fv_exp (subst_exp e2 x1 e1) [=] fv_exp e1).
Proof.
intros e1 e2 x1.
simp_stlc. generalize dependent 0.
dependent induction e1.
all: intros e2.
all: simp_stlc. 
all: default_simp.
Qed.

(* end hide *)

Lemma fv_exp_subst_exp_fresh :
forall e1 e2 x1,
  x1 `notin` fv_exp e1 ->
  fv_exp (subst_exp e2 x1 e1) [=] fv_exp e1.
Proof.
pose proof fv_exp_subst_exp_fresh_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve fv_exp_subst_exp_fresh : lngen.
Hint Rewrite fv_exp_subst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_exp_subst_exp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fv_exp e1) [<=] fv_exp (subst_exp e2 x1 e1)).
Proof.
intros e1 e2 x1.
simp subst_exp. generalize dependent 0.
dependent induction e1.
all: intros e2.
all: simp_stlc. 
all: default_simp.
fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_subst_exp_lower :
forall e1 e2 x1,
  remove x1 (fv_exp e1) [<=] fv_exp (subst_exp e2 x1 e1).
Proof.
pose proof fv_exp_subst_exp_lower_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve fv_exp_subst_exp_lower : lngen.

(* begin hide *)

Lemma fv_exp_subst_exp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fv_exp e1 ->
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp (subst_exp e2 x1 e1)).
Proof.
intros e1 e2 x1.
simp subst_exp. generalize dependent 0.
dependent induction e1.
all: intros e2.
all: simp_stlc. 
all: default_simp.
eapply IHe1. auto. simp_stlc.
Qed.

(* end hide *)

Lemma fv_exp_subst_exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_exp e1 ->
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp (subst_exp e2 x1 e1).
Proof.
pose proof fv_exp_subst_exp_notin_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve fv_exp_subst_exp_notin : lngen.

(* begin hide *)

Lemma fv_exp_subst_exp_upper_mutual :
(forall e1 e2 x1,
  fv_exp (subst_exp e2 x1 e1) [<=] fv_exp e2 `union` remove x1 (fv_exp e1)).
Proof.
intros e1 e2 x1.
simp subst_exp. generalize dependent 0.
dependent induction e1.
all: intros e2.
all: simp_stlc. 
all: default_simp.
fsetdec.
specialize (IHe1 (weaken_exp e2)).
move:IHe1. simp weaken_exp.
Qed.

(* end hide *)

Lemma fv_exp_subst_exp_upper :
forall e1 e2 x1,
  fv_exp (subst_exp e2 x1 e1) [<=] fv_exp e2 `union` remove x1 (fv_exp e1).
Proof.
pose proof fv_exp_subst_exp_upper_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve fv_exp_subst_exp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

(* We need to make subst take an exp 0 always (and then weaken at the bottom) in order to state this lemma *)

(*
Lemma subst_exp_close_exp_wrt_exp_rec_mutual :
forall {n1} (e2 : exp n1) (e1 : exp n1) x1 x2,
  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  subst_exp_rec e1 x1 (close_exp_wrt_exp_rec x2 e2) = close_exp_wrt_exp_rec x2 (subst_exp_rec e1 x1 e2).
Proof.
intros. 
funelim (subst_exp_rec e1 x1 e2).
all: simp_stlc.
all: default_simp.
Qed.

(* end hide *)

Lemma subst_exp_close_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  subst_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp e1 x1 e2).
Proof.
pose proof subst_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve subst_exp_close_exp_wrt_exp_rec : lngen.

Lemma subst_exp_close_exp_wrt_exp :
forall e2 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fv_exp e1 ->
  subst_exp e1 x1 (close_exp_wrt_exp x2 e2) = close_exp_wrt_exp x2 (subst_exp e1 x1 e2).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[global] Hint Resolve subst_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_degree_exp_wrt_exp_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_degree_exp_wrt_exp :
forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp e2 x1 e1).
Proof.
pose proof subst_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve subst_exp_degree_exp_wrt_exp : lngen.
*)

(* begin hide *)

Lemma subst_exp_fresh_eq_mutual :
(forall n (e2 e1 : exp n) x1,
  x1 `notin` fv_exp e2 ->
  subst_exp_rec e1 x1 e2 = e2).
Proof.
intros n e2 e1 x1.
dependent induction e2.
all: simp_stlc. 
all: default_simp.
Qed.

#[global] Hint Resolve subst_exp_fresh_eq_mutual : lngen.
Hint Rewrite subst_exp_fresh_eq_mutual using solve [auto] : lngen.


(* end hide *)

Lemma subst_exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_exp e2 ->
  subst_exp e1 x1 e2 = e2.
Proof.
  intros. simp_stlc.
pose proof subst_exp_fresh_eq_mutual as h; intuition eauto.
Qed.

#[global] Hint Resolve subst_exp_fresh_eq : lngen.
Hint Rewrite subst_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (subst_exp e1 x1 e2)).
Proof.
intros e2 e1 x1.
simp subst_exp. generalize dependent 0.
dependent induction e2.
all: intros e1.
all: simp_stlc. 
all: default_simp.
specialize (IHe2 (weaken_exp e1)). 
eapply IHe2. simp_stlc.
Qed.


(* end hide *)

Lemma subst_exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (subst_exp e1 x1 e2).
Proof.
pose proof subst_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve subst_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_exp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (subst_exp e1 x2 e2)).
Proof.
intros e2 e1 x1 x2.
simp subst_exp. generalize dependent 0.
dependent induction e2.
all: intros e1.
all: simp_stlc. 
all: default_simp.
specialize (IHe2 (weaken_exp e1)); eapply IHe2; simp_stlc.
Qed.

(* end hide *)

Lemma subst_exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_exp e2 ->
  x1 `notin` fv_exp e1 ->
  x1 `notin` fv_exp (subst_exp e1 x2 e2).
Proof.
pose proof subst_exp_fresh_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve subst_exp_fresh : lngen.

(*
Lemma subst_exp_lc_exp :
forall e1 e2 x1,
  lc_exp e1 ->
  lc_exp e2 ->
  lc_exp (subst_exp e2 x1 e1).
Proof.
default_simp.
Qed.

#[global] Hint Resolve subst_exp_lc_exp : lngen.
*)

Lemma subst_exp_rec_weaken_exp : forall n (e1 : exp n) x1 u,
 subst_exp_rec (weaken_exp e1) x1 (weaken_exp u) = weaken_exp (subst_exp_rec e1 x1 u).
Proof.
  intros.
  funelim (weaken_exp u); simp_stlc; default_simp.
Qed.

#[global] Hint Resolve subst_exp_rec_weaken_exp : lngen.
Hint Rewrite subst_exp_rec_weaken_exp : lngen.


(* begin hide *)

Lemma subst_exp_open_exp_wrt_exp_rec_mutual :
(forall n1 (e1 : exp n1) e2 (e3 : exp (S n1)) x1,
  subst_exp_rec e1 x1 (open_exp_wrt_exp_rec e2 e3) = open_exp_wrt_exp_rec (subst_exp_rec e1 x1 e2) (subst_exp_rec (weaken_exp e1) x1 e3)).
Proof.
intros n1 e1 e2 e3 x1.
funelim (open_exp_wrt_exp_rec e2 e3).
all: simp_stlc. 
all: default_simp.
destruct (decrease_fin k f) eqn:E1.
simp_stlc. auto. auto.
rewrite H.
default_simp.
Qed.

(* end hide *)

(* begin hide *)

(* SCW: this one also might be simpler if we only substitute 
   locally closed terms *)
Lemma subst_exp_open_exp_wrt_exp_rec :
forall n1 (e3 : exp (S n1)) e1 e2 x1,
  subst_exp_rec e1 x1 (open_exp_wrt_exp_rec e2 e3) = 
    open_exp_wrt_exp_rec (subst_exp_rec e1 x1 e2) 
                         (subst_exp_rec (weaken_exp e1) x1 e3).
Proof.
pose proof subst_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve subst_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  subst_exp e1 x1 (open_exp_wrt_exp e3 e2) = 
    open_exp_wrt_exp (subst_exp_rec (weaken_exp e1) x1 e3) (subst_exp e1 x1 e2).
Proof.
 intros.
 simp subst_exp.
 simp_stlc.
 default_simp.
Admitted.

#[global] Hint Resolve subst_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_open_exp_wrt_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  open_exp_wrt_exp (subst_exp_rec (weaken_exp e1) x1 e2) (var_f x2) = 
    subst_exp e1 x1 (open_exp_wrt_exp e2 (var_f x2)).
Proof.
intros; rewrite subst_exp_open_exp_wrt_exp; default_simp.
Qed.

#[global] Hint Resolve subst_exp_open_exp_wrt_exp_var : lngen.

(* begin hide *)

Lemma subst_exp_spec_rec_mutual :
(forall n (e1 e2 : exp n) x1,
  subst_exp_rec e2 x1 e1 = open_exp_wrt_exp_rec e2 (close_exp_wrt_exp_rec  x1 e1)).
Proof.
intros n e1 e2 x1.
dependent induction e1.
all: simp_stlc. 
all: default_simp.
simp_stlc. auto.
Qed.


(* end hide *)

(* begin hide *)

Lemma subst_exp_spec_rec :
forall n (e1 e2 : exp n) x1,
  subst_exp_rec e2 x1 e1 = open_exp_wrt_exp_rec e2 (close_exp_wrt_exp_rec x1 e1).
Proof.
pose proof subst_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve subst_exp_spec_rec : lngen.

(* end hide *)

Lemma subst_exp_spec :
forall e1 e2 x1,
  subst_exp e2 x1 e1 = open_exp_wrt_exp (close_exp_wrt_exp x1 e1) e2.
Proof.
intros. simp_stlc. default_simp.
Qed.

#[global] Hint Resolve subst_exp_spec : lngen.

(* begin hide *)

Lemma subst_exp_subst_exp_mutual :
(forall n (e1 e2 e3 : exp n) x2 x1,
  x2 `notin` fv_exp e2 ->
  x2 <> x1 ->
  subst_exp_rec e2 x1 (subst_exp_rec e3 x2 e1) = 
    subst_exp_rec (subst_exp_rec e2 x1 e3) x2 (subst_exp_rec e2 x1 e1)).
Proof.
intros n e1.
dependent induction e1; intros.
all: simp_stlc. 
all: default_simp.
all: simp_stlc. 
all: default_simp.
rewrite IHe1. 
all: simp_stlc.
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_subst_exp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_exp e2 ->
  x2 <> x1 ->
  subst_exp e2 x1 (subst_exp e3 x2 e1) = subst_exp (subst_exp e2 x1 e3) x2 (subst_exp e2 x1 e1).
Proof.
intros.
eapply subst_exp_subst_exp_mutual. auto. auto.
(* pose proof subst_exp_subst_exp_mutual as H; intuition eauto. *)
Qed.

#[global] Hint Resolve subst_exp_subst_exp : lngen.

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall n1 (e2 : exp (S n1)) e1 x1 x2,
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  subst_exp_rec (weaken_exp e1) x1 e2 = 
    close_exp_wrt_exp_rec x2 
       (subst_exp_rec e1 x1 (open_exp_wrt_exp_rec (var_f x2) e2))).
Proof.
intros n e2.
dependent induction e2; intros.
all: simp_stlc. 
all: default_simp.
all: try destruct (decrease_fin n f) eqn:E.
all: default_simp.
all: simp_stlc. 
all: default_simp.
symmetry. eauto using decrease_increase_fin.
symmetry. eauto using decrease_to_fin.
specialize (IHe2 _ e2 ltac:(auto) ltac:(auto)).
specialize (IHe2 (weaken_exp e1)).
eapply IHe2; eauto.
all: simp_stlc. 
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall n1 (e2 : exp (S n1)) e1 x1 x2,
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  subst_exp_rec (weaken_exp e1) x1 e2 = close_exp_wrt_exp_rec  x2 (subst_exp_rec e1 x1 (open_exp_wrt_exp_rec (var_f x2) e2)).
Proof.
pose proof subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[global] Hint Resolve subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall (e2 : exp 1) (e1 : exp 0) x1 x2,
  x2 `notin` fv_exp e2 ->
  x2 `notin` fv_exp e1 ->
  x2 <> x1 ->
  subst_exp_rec (weaken_exp e1) x1 e2 =
    close_exp_wrt_exp x2 (subst_exp_rec e1 x1 (open_exp_wrt_exp e2 (var_f x2))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[global] Hint Resolve subst_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_abs :
forall x2 (e2 : exp 1) (e1 : exp 0) x1,
  x2 `notin` fv_exp e1 `union` fv_exp e2 `union` singleton x1 ->
  subst_exp e1 x1 (abs e2) = abs (close_exp_wrt_exp x2 (subst_exp e1 x1 (open_exp_wrt_exp e2 (var_f x2)))).
Proof.
default_simp. simp_stlc. default_simp.
Qed.

#[global] Hint Resolve subst_exp_abs : lngen.

(* begin hide *)
Lemma subst_exp_intro_rec :
forall n1 (e1 : exp (S n1)) x1 e2,
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp_rec e2 e1 = subst_exp_rec e2 x1 (open_exp_wrt_exp_rec (var_f x1) e1).
Proof.
dependent induction e1; default_simp.
all: simp_stlc.
all: try destruct decrease_fin eqn:E.
all: simp_stlc.
all: default_simp.
Qed.

#[global] Hint Resolve subst_exp_intro_rec : lngen.
Hint Rewrite subst_exp_intro_rec using solve [auto] : lngen.

(* end hide *)

Lemma subst_exp_intro :
forall x1 e1 e2,
  x1 `notin` fv_exp e1 ->
  open_exp_wrt_exp e1 e2 = subst_exp e2 x1 (open_exp_wrt_exp e1 (var_f x1)).
Proof.
unfold open_exp_wrt_exp; default_simp.
simp_stlc.
default_simp.
Qed.

#[global] Hint Resolve subst_exp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
