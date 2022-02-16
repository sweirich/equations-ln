(***********************************************************************)
(** * Definition of Finite numbers *)
(***********************************************************************)

(* Bound variables are represented using the 'fin' datatype shown below. 
The key idea is the index of this type says how many elements it has. For 
example, the type [fin 0] is an empty type, the type [fin 1] only has a 
single value [fO], the type [fin 2] has two values ([fO] and [fS fO]). *)

(* ----------- imports --------------- *)
Require Import Program.Basics Program.Combinators.
From Equations Require Import Equations.
Require Import Coq.Program.Equality. 

(* these first few definitions are from equations example 
   https://github.com/mattam82/Coq-Equations/blob/master/examples/Fin.v  *)

Inductive fin : nat -> Set :=
  | fO : forall {n}, fin (S n)
  | fS : forall {n}, fin n -> fin (S n).

Derive Signature NoConfusionHom NoConfusion for fin.

(** We can inject it into [nat]. *)
Equations fog {n} (f : fin n) : nat :=
fog (n:=?(S n)) (@fO n) := 0 ;
fog (fS f) := S (fog f).

(** The injection preserves the number: *)
Lemma fog_inj {n} (f : fin n) : fog f < n.
Proof with auto with arith. intros.
  depind f; simp fog...
Qed.

(** Of course it has an inverse. *)

(* coerce a natural number to the fin with the smallest possible 
   range. *)
Equations gof n : fin (S n) :=
gof O := fO ;
gof (S n) := fS (gof n).

Lemma fog_gof n : fog (gof n) = n.
Proof with auto with arith.
  intros. funelim (gof n)... simp fog; congruence.
Qed.

Equations fin_inj_one {n} (f : fin n) : fin (S n) :=
fin_inj_one fO := fO;
fin_inj_one (fS f) := fS (fin_inj_one f).

Inductive le : nat -> nat -> Type :=
| le_O n : 0 <= n
| le_S {n m} : n <= m -> S n <= S m
where "n <= m" := (le n m).
Derive Signature for le.

Equations le_S_inv {n m} (p : S n <= S m) : n <= m :=
le_S_inv (le_S p) := p.

Equations fin_inj {n} {m} (f : fin n) (k : n <= m) : fin m :=
fin_inj fO (le_S p) := fO;
fin_inj (fS f) (le_S p) := fS (fin_inj f p).

(** Let's do some arithmetic on [fin] *)

Inductive finle : forall (n : nat) (x : fin n) (y : fin n), Prop :=
| leqz : forall {n j}, finle (S n) fO j
| leqs : forall {n i j}, finle n i j -> finle (S n) (fS i) (fS j).

Scheme finle_ind_dep := Induction for finle Sort Prop.

Instance finle_ind_pack n x y : DepElim.DependentEliminationPackage (finle n x y) :=
  { elim_type := _ ; elim := finle_ind_dep }.

Arguments finle {n}.

(** Additional definitions and properties for fin *)

(* equality is derivable *)

Derive EqDec for fin.

(* 
Equations fin_beq {n}  (f g : fin n) : bool :=
  fin_beq fO fO := true;
  fin_beq (n:=?(S n')) (fS f) (fS (n:=n') f')  := 
    fin_beq f f';
  fin_beq x y := false.

Equations fin_eq_dec {n} (f g : fin n) : 
   { f = g } + { f <> g } :=
fin_eq_dec fO fO := left eq_refl;
fin_eq_dec (n:=?(S n')) (fS f) (fS (n:=n') f') 
  with fin_eq_dec f f' := 
  { | left eq_refl => left eq_refl;
    | right p => right _ };
fin_eq_dec x y := right _.
*)

(* coerce m to a smaller range, as long as it is not 0. 
   does not change the value of m. *)
(* used in "open" *)
Equations decrease_fin (k : nat) (m : fin (S k)) : option (fin k) :=
  decrease_fin O _ := None ;
  decrease_fin (S _) fO := Some fO;
  decrease_fin (S m) (fS n) := option_map fS (decrease_fin m n).


(* coerce m to a larger range. does not change the value of m. *)
(* used in "close" operation. *)
Equations increase_fin {n : nat} (m : fin n) : fin (S n) :=
  increase_fin (@fO n1) := fO;
  increase_fin (@fS n1 m) := fS (increase_fin m). 

(* 
pf : a + b = b + a

match pf with 
 | eq_refl => ...
end

eta rules

function:
if a : A -> B then  a = \x. a x

[empty context]
|- a : A -> B then  a ~>* \y. a'   [type soundness]

    a = (\y.a')  ==?  \x. (\y.a') x  == \x. a'{x/y}

product
if a : A * B then a = (fst a, snd a)

unit
if a : unit  then a = ()

equality type (axiom K)

if a : A = B then a = refl



*)

(* coerce m to a much larger range. does not change the value of m. *)
Equations weaken_fin {n : nat} (k:nat) (m : fin n) : fin (n + k) :=
  weaken_fin k fO := fO ;
  weaken_fin k (fS f) := fS (weaken_fin k f).
(*
Equations to_fin (n : nat) : fin (S n) :=
  to_fin O     := fO ;
  to_fin (S m) := fS (to_fin m).
*)

(* Theory *)

(* increase_fin is injective *)
Lemma increase_fin_inj : forall {n} (f f0 : fin n),
    (increase_fin f = increase_fin f0) -> f = f0.
Proof.
  intros n f g.
  funelim (increase_fin f).
  all: dependent elimination g; simp increase_fin. 
  all: intros h; noconf h; auto.
  f_equal; auto.
Qed.

(* decrase fin is injective *)
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
  forall {n1} (f0 : fin n1) (f : fin (S n1)),  decrease_fin n1 f = Some f0 -> increase_fin f0 = f.
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



Lemma decrease_fin_increase_fin : forall n1 (f : fin n1), decrease_fin n1 (increase_fin f) = Some f.
Proof. 
  intros.
  dependent induction f.
  all: simp increase_fin.
  all: simp decrease_fin.
  all: auto.
  rewrite IHf.
  reflexivity.
Qed.

Lemma decrease_fin_gof : forall n, decrease_fin n (gof n) = None.
Proof.
  induction n.
  all: simp gof. 
  all: simp decrease_fin. 
  auto. rewrite IHn. 
  reflexivity.
Qed.

Hint Rewrite decrease_fin_increase_fin : decrease_fin.
Hint Rewrite decrease_fin_gof : decrease_fin.
