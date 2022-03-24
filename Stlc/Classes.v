Require Import Metalib.Metatheory.
Require Import Metalib.LibLNgen.
From Equations Require Import Equations.

(***********************************************************************)
(** * Operations *)
(***********************************************************************)

(* Syntactic operations on terms of type `e n`, i.e. those that contain 
   at most `n` bound variables. We call `n` the "scope index" --- number 
   of bound variables that are in scope. (The set of allowed free variables
   is not tracked by the type system.)
*)
   

Class Syntax (e : nat -> Set) := {

    (* List free variables *)
    fv : forall {n}, e n -> vars ;

    (* Count number of nodes in AST *)
    size : forall {n}, e n -> nat ;

    (* Increase the scope index, but do not modify the term *)
    weaken : forall {n}, e n -> e (S n) ;

    (* Replace the given free variable with bound variable `n`, increasing
       the scope of the term. *)
    close : forall {n}, var -> e n -> e (S n) ;
}.


(* Substitution operations.  

   This class is indexed by two types so that it can include, for example,
   substituting types in terms as well as substituting terms in terms. 
   This is more general than needed for STLC, but adds flexibility to 
   the overall approach.

*)

Class Subst (e : nat -> Set) (u : nat -> Set) `{Syntax e} `{Syntax u} := {

    (* bound variable substitution

       Replaces bound variable n with a term of type `u n` inside a 
       term of type `e (S n)`. Because we are replacing the largest index
       we can decrement the scope.
     *)
    open  : forall {n}, u n -> e (S n) -> e n ;

    (* free variable substitution

       Replaces free variable by term of type `u n` in an expression
       of type `e n`. Doesn't change the scoping of bound variables.
     *)

    subst : forall {n}, u n -> var -> e n -> e n    
}.

(***********************************************************************)
(** * Theory *)
(***********************************************************************)

(* These are the general form of the lemmas in the Lemmas.v file. *)

(* Properties about operations in the `Syntax` class. *)   

Class SyntaxTheory (exp : nat -> Set) `{H: Syntax exp} := {

    size_weaken : forall n (t : exp n), size (weaken t) = size t;

    fv_weaken : forall n1 (e1 : exp n1), fv (weaken e1) = fv e1;
    
    size_min : forall n (e : exp n), 1 <= size e;
    
    size_close : forall n (e1 : exp n) x1, 
      size (close x1 e1) = size e1;
    
    close_inj : forall k (e1 : exp k) e2 x1,
      close x1 e1 = close x1 e2 ->
      e1 = e2;

   close_weaken : forall n1 (e1 : exp n1) x1,
      x1 `notin` fv e1 ->
      close x1 e1 = weaken e1;

    fv_close : forall n1 (e1 : exp n1) x1,
      fv (close x1 e1) [=] remove x1 (fv e1);
}.

(* Properties about the substitution operations (and their 
   interaction with the operations in the Syntax class). *)

Class SubstTheory (exp : nat -> Set) (u : nat -> Set) 
      `{H: Subst exp u} := {
    
    size_open : forall k (e1 : exp (S k)) (e2 :u k),
      size e1 <= size (open e2 e1);
        
    open_weaken : forall n1 (e2 : exp n1) e1,
      open e1 (weaken e2) = e2;

    fv_open_lower : forall n1 (e1 : exp (S n1)) e2,
      fv e1 [<=] fv (open e2 e1);

    fv_open_upper : forall n1 (e1 : exp (S n1)) e2,
      fv (open e2 e1) [<=] fv e2 `union` fv e1;


    fv_subst_fresh : forall n1 (e1 : exp n1) e2 x1,
      x1 `notin` fv e1 ->
      fv (subst e2 x1 e1) [=] fv e1;

    fv_subst_lower : forall n1 (e1 : exp n1) e2 x1,
      remove x1 (fv e1) [<=] fv (subst e2 x1 e1);

    fv_subst_notin : forall n1 (e1 : exp n1) e2 x1 x2,
      x2 `notin` fv e1 ->
      x2 `notin` fv e2 ->
      x2 `notin` fv (subst e2 x1 e1);

    fv_subst_upper : forall n1 (e1 : exp n1) e2 x1,
      fv (subst e2 x1 e1) [<=] fv e2 `union` remove x1 (fv e1);  

    subst_close : forall n1 (e2 : exp n1) e1 x1 x2,
      x1 <> x2 ->
      x2 `notin` fv e1 ->
      subst (weaken e1) x1 (close x2 e2) =
        close x2 (subst e1 x1 e2);

    subst_fresh_eq : forall n1 (e2 : exp n1) e1 x1,
      x1 `notin` fv e2 ->
      subst e1 x1 e2 = e2;
    
    subst_fresh_same : forall n1 (e2 : exp n1) e1 x1,
      x1 `notin` fv e1 ->
      x1 `notin` fv (subst e1 x1 e2);


    subst_weaken : forall n u1 x1 (e1:exp n),
      weaken (subst u1 x1 e1) = 
        subst (weaken u1) x1 (weaken e1);  

   subst_spec : forall n (e1 : exp n) e2 x1,
      subst e2 x1 e1 = open e2 (close x1 e1);
                                                          
  }.

(* Properties about the substitution operations that also 
   refer to the free variable constructor for `u` terms.
   We generalize this constructor as an additional parameter
   to the type class.
 *)


Class SubstVarTheory (exp : nat -> Set) (u : nat -> Set) 
      (uvar : forall {n}, var -> u n) `{H: Subst exp u} := {

    size_open_var : forall k (e : exp (S k)) x,
      size (open (uvar x) e) = size e;

    close_open : forall n1 (e1 : exp (S n1)) x1 ,
      x1 `notin` fv e1 ->
      close x1 (open (uvar x1) e1) = e1;

    open_close : forall n1 (e1 : exp n1) x1,
      open (uvar x1) (close x1 e1) = e1;
    
    open_inj : forall n1 (e2 e1:exp (S n1)) x1,
      x1 `notin` fv e2 ->
      x1 `notin` fv e1 ->
      open (uvar x1) e2 = open (uvar x1) e1 ->
      e2 = e1;

   subst_open_var : forall n1 (e2 : exp (S n1)) e1 x1 x2,
        x1 <> x2 ->
        open (uvar x2) (subst (weaken e1) x1 e2) = 
          subst e1 x1 (open (uvar x2) e2);

   subst_close_open : forall n1 (e2 : exp (S n1)) e1 x1 x2,
      x2 `notin` fv e2 ->
      x2 `notin` fv e1 ->
      x2 <> x1 ->
      subst (weaken e1) x1 e2 = 
      close x2 
       (subst e1 x1 (open (uvar x2) e2)); 

   subst_intro  : forall n (e1 : exp (S n)) (x1:var) (e2 : u n),
      x1 `notin` fv e1 ->
      open e2 e1 = subst e2 x1 (open (uvar x1) e1) ;
}.

(* Properties about the substitution operation that 
   require distributing substitutions to both `exp` terms 
   and `u` terms. *)

Class SubstSubstTheory (exp : nat -> Set) (u : nat -> Set) 
      `{H: Subst exp u}`{HU: Subst u u} := {

    subst_open : forall n1 (e1 : u n1) e2 (e3 : exp (S n1)) x1,
      subst e1 x1 (open e2 e3) =
        open (subst e1 x1 e2) (subst (weaken e1) x1 e3);  
    
    subst_subst : forall n (e1 : exp n) e2 e3 x2 x1,
      x2 `notin` fv e2 ->
      x2 <> x1 ->
      subst e2 x1 (subst e3 x2 e1) = 
        subst (subst e2 x1 e3) x2 (subst e2 x1 e1); 
  }.



(***********************************************************************)
(** * Rewriting / tactics *)
(***********************************************************************)

Create HintDb syntax.

#[export] Hint Rewrite @close_open
  using solve [auto; try typeclasses eauto] : syntax.

#[export] Hint Rewrite @open_close
  using solve [auto; try typeclasses eauto] : syntax.

#[export] Hint Rewrite @subst_open_var
  using solve [auto; try typeclasses eauto] : syntax.


Create HintDb fv.
Create HintDb open.
Create HintDb close.
Create HintDb weaken.
Create HintDb size.
Create HintDb subst.

(* The idea of this tactic is that each of the operations in 
   the `Syntax` and `Subst` classes come with their own library
   of rewriting hints. We can apply them all, repeatedly, using 
   the following tactic. *)

Ltac simp_syntax := repeat first [ 
                       simp subst
                     || simp open
                     || simp close
                     || simp weaken
                     || simp size
                     || simp fv
                     || simp syntax
                     ].



(***********************************************************************)
(** * Notations *)
(***********************************************************************)

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definition provides a
    convenient shorthand for such uses.  Note that the order of
    arguments is switched relative to the definition above.  For
    example, [e ^ fvar x] can be read as "substitute the free 
    variable [x] for index [0] in [e]".
*)

Declare Scope syntax_scope.
Module SyntaxNotations.
Notation "[ z ~> u ] e" := (subst u z e) (at level 0) : syntax_scope.
Notation "e ^ x"        := (open x e) : syntax_scope.
End SyntaxNotations.


