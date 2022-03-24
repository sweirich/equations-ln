Require Export Metalib.Metatheory.
Require Export Stlc.Classes.
Require Import Stlc.DefinitionsSyntax.
Require Import Stlc.ClassInstances.

(* Tactics for simplifying syntax definitions *)

Lemma fv_exp_var_b : forall n (m: fin n), fv (var_b m) = {}. 
Proof. reflexivity. Qed.
Lemma fv_exp_var_f : forall n (x:atom), fv (var_f (n:=n) x) = {{x}}.
Proof. reflexivity. Qed.
Lemma fv_exp_abs : forall n (e: exp (S n)), fv (abs e) = fv e.
Proof. reflexivity. Qed.
Lemma fv_exp_app : forall n (e1 : exp n) (e2: exp n), fv (app e1 e2) = fv e1 `union` fv e2.
Proof. reflexivity. Qed.

#[export] Hint Rewrite fv_exp_var_b fv_exp_var_f fv_exp_abs fv_exp_app : fv.

(* Re-define behavior of size in terms of size_exp *)
Lemma size_exp_var_b : forall n (m: fin n), size (var_b m) = 1. 
Proof. reflexivity. Qed.
Lemma size_exp_var_f : forall n (x:atom), size (var_f (n:=n) x) = 1.
Proof. reflexivity. Qed.
Lemma size_exp_abs : forall n (e: exp (S n)), size (abs e) = 1 + (size e).
Proof. reflexivity. Qed.
Lemma size_exp_app : forall n (e1 : exp n) (e2: exp n), size (app e1 e2) = 1 + size e1 + size e2.
Proof. reflexivity. Qed.

#[export] Hint Rewrite size_exp_var_b size_exp_var_f size_exp_abs size_exp_app : size.

Lemma weaken_exp_var_b : forall n (m: fin n),   weaken  (var_b m) = var_b (increase_fin m).
Proof. reflexivity. Qed.
Lemma weaken_exp_var_f : forall n (x:atom), weaken (var_f (n:=n) x) = var_f x.
Proof. reflexivity. Qed.
Lemma weaken_exp_abs : forall n (e: exp (S n)), weaken (abs e) = abs (weaken e).
Proof. reflexivity. Qed.
Lemma weaken_exp_app : forall n (e1 : exp n) (e2: exp n), weaken (app e1 e2) = app (weaken e1) (weaken e2).
Proof. reflexivity. Qed.

#[export] Hint Rewrite weaken_exp_var_b weaken_exp_var_f weaken_exp_abs weaken_exp_app : weaken.

Lemma close_exp_var_b : forall n x (m: fin n),   close x (var_b m) = var_b (increase_fin m).
Proof. reflexivity. Qed.
Lemma close_exp_var_f : forall n (x1 x2:atom), close x1 (var_f (n:=n) x2) = if (x1 == x2) then (var_b (gof n)) else (var_f x2).
Proof. reflexivity. Qed.
Lemma close_exp_abs : forall n (e: exp (S n)) x1, close x1 (abs e) = abs (close x1 e).
Proof. reflexivity. Qed.
Lemma close_exp_app : forall n (e1 : exp n) (e2: exp n) x1, close x1 (app e1 e2) = app (close x1 e1) (close x1 e2).
Proof. reflexivity. Qed.

#[export] Hint Rewrite close_exp_var_b close_exp_var_f close_exp_abs close_exp_app : close.

Lemma open_exp_var_b : forall n (u:exp n) (m: fin (S n)), 
    open u (var_b m) = 
      match decrease_fin n m with
      | Some f => var_b f
      | None => u
      end.
Proof. reflexivity. Qed.
Lemma open_exp_var_f : forall n (u:exp n) (x:atom), open u (var_f (n:= S n) x) = var_f x.
Proof. reflexivity. Qed.

Lemma open_exp_abs : forall n (u:exp n) (e: exp (S (S n))), 
    open u (abs e) = abs (open (weaken u) e).
Proof. reflexivity. Qed. 
Lemma open_exp_app : forall n (u:exp n) (e1 : exp (S n)) (e2: exp (S n)), 
    open u (app e1 e2) = app (open u e1) (open u e2).
Proof. reflexivity. Qed.

#[export] Hint Rewrite open_exp_var_b open_exp_var_f open_exp_abs open_exp_app : open.

Lemma subst_exp_var_b : forall n (u:exp n) (y:atom) (m: fin n), 
    subst u y (var_b m) = var_b m.
Proof. reflexivity. Qed.
Lemma subst_exp_var_f : forall n (u:exp n) (y:atom) (x:atom), 
    subst u y (var_f (n:=n) x) = if x == y then u else var_f x.
Proof. reflexivity. Qed.
Lemma subst_exp_abs : forall n (u:exp n) (y:atom) (e: exp (S n)), 
    subst u y (abs e) = abs (subst (weaken u) y e).
Proof. reflexivity. Qed.
Lemma subst_exp_app : forall n (u:exp n) (y:atom) (e1 : exp n) (e2: exp n), 
    subst u y (app e1 e2) = app (subst u y e1) (subst u y e2).
Proof. reflexivity. Qed.

#[export] Hint Rewrite subst_exp_var_b subst_exp_var_f subst_exp_abs subst_exp_app : subst.
