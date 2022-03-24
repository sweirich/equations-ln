(***********************************************************************)
(** * Definition of Finite numbers *)
(***********************************************************************)

(* Bound variables are represented using the 'fin' datatype shown below.

   Elements of fin n can be seen as natural numbers in the set {m | m < n}.

   The key idea is the index of this type says how many elements the type
   has. For example, the type [fin 0] is an empty type, the type [fin 1] only
   has a single value [fO], the type [fin 2] has two values ([fO] and [fS
   fO]), etc.  

   Some definitions in this library are from equations example 
   https://github.com/mattam82/Coq-Equations/blob/master/examples/Fin.v 

   There is a lot more we can do with [fin], but this is enough for 
   STLC (and we don't need all of it).

*)

(* ----------- imports --------------- *)
Require Import Program.Basics Program.Combinators.
From Equations Require Import Equations.
Require Import Coq.Program.Equality. 
Require Import Nat.
Require Import Lia.

Inductive fin : nat -> Set :=
  | fO : forall {n}, fin (S n)
  | fS : forall {n}, fin n -> fin (S n).

Derive Signature NoConfusionHom NoConfusion for fin.

(* decidable equality is derivable *)
Derive EqDec for fin.

(* ------- type coercions ------ *)

(* Coerce [m] to a smaller range, as long as it is not k. 
   does not change the "value" of [m]. *)
(* NB: used in "open" *)
Equations decrease_fin (k : nat) (m : fin (S k)) : option (fin k) :=
  decrease_fin O _ := None ;
  decrease_fin (S _) fO := Some fO;
  decrease_fin (S m) (fS n) := option_map fS (decrease_fin m n).

(* Coerce [m] to a larger range, without changing its value. *)
(* NB: used in "close" operation. *)
Equations increase_fin {n : nat} (m : fin n) : fin (S n) :=
  increase_fin fO  := fO;
  increase_fin (fS m) := fS (increase_fin m). 

(* -------- isomorphism with {m : nat | m < n} ------- *)

(* Coerce between [fin] and [nat], preserving value.

    f0 <-> O
    fS f0 <-> S O
    fS (fS f0) <-> S (S O)
*)
  
(* We can inject [fin n] into [nat]. Forget the rich type. *)
Equations fog {n} (f : fin n) : nat :=
  fog fO     := 0 ;
  fog (fS f) := S (fog f).

Print fog_graph.

(* And come back again. Note: we produce a [fin] with the 
   smallest possible range. *)
Equations gof (n : nat) : fin (S n) :=
  gof O := fO ;
  gof (S n) := fS (gof n).

Print fog.
Print gof.

(* ------- properties of definitions above ------- *)

Lemma fog_gof (n : nat) : fog (gof n) = n.
Proof with auto with arith.
  intros. funelim (gof n). info_auto.
  simp fog. congruence.
Qed.

Lemma fog_inj {n} (f : fin n) : fog f < n.
Proof with auto with arith. 
  intros.
  funelim (fog f); simp fog...
(*  induction f; simp fog...
  dependent induction f; simp fog...
  depind f; simp fog... *)
Qed.

Require Import Coq.Logic.EqdepFacts.

(* increase_fin is injective *)
Lemma increase_fin_inj : forall {n} (f f0 : fin n),
    (increase_fin f = increase_fin f0) -> f = f0.
Proof.
  intros n f g.
  funelim (increase_fin f).
  all: dependent elimination g; simp increase_fin.
  auto.
  intros h. inversion h.
  intros h. inversion h.
  intros h. 
  noconf h. f_equal. auto.   (* no axiom *)
  (* These two proofs work, but need an axiom *)
(*  inversion h. dependent destruction H1. f_equal. auto. *)
(*  inversion h. apply Eqdep.EqdepTheory.inj_pair2 in H1.
  f_equal. auto. *)
Qed.

Print Assumptions increase_fin_inj.

(* decrease fin is injective *)
Lemma decrease_fin_inj : forall {n} (f f0 : fin (S n)),
    (decrease_fin n f = decrease_fin n f0) -> f = f0.
Proof.
  intros.
  dependent induction n;
  dependent elimination f;
  dependent elimination f0; auto.    
  all: try solve [dependent elimination f].
  all: try simp decrease_fin in H.
  all: destruct (decrease_fin n f) eqn: E1.
  all: try destruct (decrease_fin n f0) eqn: E2.
  all: simpl in H.
  all: try discriminate.
  all: noconf H.
  all: rewrite <- E2 in E1.
  all: eapply IHn in E1.
  all: f_equal; auto.
Qed.
  
(* increase always produces a number less than the max. *)
Lemma increase_not_n : forall {n}(f : fin n), 
         not (gof n = increase_fin f).
Proof. 
  intros.
  dependent induction n;
  dependent elimination f;
  simp gof; simp increase_fin.
  intros h. noconf h. 
  intros h. noconf h. eapply IHn. eauto.
Qed.


(* If we can decrease a fin, then increasing it gives us the same number. *)
Lemma decrease_increase_fin :
  forall {n1} (f0 : fin n1) (f : fin (S n1)),  
    decrease_fin n1 f = Some f0 -> increase_fin f0 = f.
Proof.
  intros.
  dependent induction f.
  destruct n1. inversion f0. simp decrease_fin in H. 
  inversion H. simp increase_fin. auto.
  destruct n1. inversion f0. simp decrease_fin in H. 
  destruct (decrease_fin n1 f) eqn:E1. simpl in H. inversion H.
  eapply IHf in E1; eauto. simp increase_fin. f_equal. auto.
  simpl in H. discriminate.
Qed.  

(* If we cannot decrease a fin, then we must have started with the maximum value. *)
Lemma decrease_to_fin : 
  forall {n1} (f: fin (S n1)), decrease_fin n1 f = None -> gof n1 = f.
Proof.
  intros.
  dependent induction f.
  destruct n1; simp decrease_fin in H; simp gof. auto. discriminate.
  destruct n1; simp decrease_fin in H; simp gof. 
  inversion f.
  destruct (decrease_fin n1 f) eqn:E1. simpl in H. inversion H.
  eapply IHf in E1; eauto. f_equal. auto.
Qed.

(* If we had increased first, we can decrease *)
Lemma decrease_fin_increase_fin : 
  forall n1 (f : fin n1), decrease_fin n1 (increase_fin f) = Some f.
Proof. 
  intros.
  dependent induction f.
  all: simp increase_fin.
  all: simp decrease_fin.
  all: auto.
  rewrite IHf.
  reflexivity.
Qed.

(* Since gof gives us the largest number in the range, we cannot decrease it. *)
Lemma decrease_fin_gof : forall n, decrease_fin n (gof n) = None.
Proof.
  induction n.
  all: simp gof. 
  all: simp decrease_fin. 
  auto. rewrite IHn. 
  reflexivity.
Qed.

Create HintDb fin.
#[export] Hint Rewrite fog_gof : fin.
#[export] Hint Rewrite decrease_fin_increase_fin : fin.
#[export] Hint Rewrite decrease_fin_gof : fin.
#[export] Hint Resolve decrease_to_fin : fin.
#[export] Hint Resolve decrease_increase_fin : fin.
#[export] Hint Resolve increase_not_n : fin.

#[export] Hint Extern 1 (_ = _) => match goal with 
 | [ H : increase_fin _ = increase_fin _ |- _ ] => apply increase_fin_inj end : fin.

#[export] Hint Extern 1 (_ = _) => match goal with 
 | [ H : gof _ = increase_fin _ |- _ ] => exfalso; eapply increase_not_n end : fin.

(*

Inductive le : nat -> nat -> Type :=
| le_O n : 0 <= n
| le_S {n m} : n <= m -> S n <= S m
where "n <= m" := (le n m).
Derive Signature for le.
Hint Constructors le.
Equations le_S_inv {n m} (p : S n <= S m) : n <= m :=
le_S_inv (le_S p) := p.

Equations fin_inj {n} {m} (f : fin n) (k : n <= m) : fin m :=
fin_inj fO (le_S p) := fO;
fin_inj (fS f) (le_S p) := fS (fin_inj f p).

Lemma foo : forall m n, m <= S (n + m). Admitted.

Equations fin_plus {n m} (x : fin n) (y : fin m) : fin (n + m) := 
fin_plus (@fO n) f := fin_inj f _ ;
fin_plus (@fS n x) y := fS (fin_plus x y). 
Next Obligation. apply foo. Defined.

Print fin_plus.
Print fin_plus_obligations_obligation_1.
(** Won't pass the guardness check which diverges anyway. *)
*)

