Require Export Stlc.Classes.
Require Import Stlc.DefinitionsSyntax.
Require Import Stlc.Lemmas.

(***********************************************************************)
(** * Class  instances *)
(***********************************************************************)

#[global] Instance Syntax_exp : Syntax exp := { 
    fv := fun {n} => @fv_exp n;
    size := fun {n} => @size_exp n; 
    weaken := fun {n} =>  @weaken_exp n;
    close := fun {n} => @close_exp_wrt_exp n;
}.

#[global] Opaque Syntax_exp.

#[global] Instance Subst_exp : Subst exp exp := {
    open := fun {n} => @open_exp_wrt_exp n;
    subst := fun {n} => @subst_exp_wrt_exp n
}.
#[global] Opaque Subst_exp.


#[global] Instance STE :  SyntaxTheory exp := {
  size_weaken := size_exp_weaken_exp;
  fv_weaken := fv_exp_weaken_exp;
  size_min  := size_exp_min;
  size_close := size_exp_close_exp_wrt_exp;
  close_inj := close_exp_wrt_exp_inj;
  close_weaken := close_exp_wrt_exp_weaken_exp;
  fv_close := fv_exp_close_exp_wrt_exp;
}.


#[global] Opaque STE.

#[global] Instance SSTE : SubstTheory exp exp := {
  size_open := size_exp_open_exp_wrt_exp;
  open_weaken := open_exp_wrt_exp_weaken_exp;
  fv_open_lower := fv_exp_open_exp_wrt_exp_lower;
  fv_open_upper := fv_exp_open_exp_wrt_exp_upper; 
  fv_subst_fresh := fv_exp_subst_exp_wrt_exp_fresh;
  fv_subst_lower := fv_exp_subst_exp_wrt_exp_lower;
  fv_subst_notin := fv_exp_subst_exp_wrt_exp_notin;
  fv_subst_upper := fv_exp_subst_exp_wrt_exp_upper; 

  subst_close := subst_exp_close_exp_wrt_exp;
  subst_fresh_eq := subst_exp_wrt_exp_fresh_eq;
  subst_fresh_same := subst_exp_wrt_exp_fresh_same;
  subst_weaken := subst_exp_wrt_exp_weaken_exp;
  subst_spec := subst_exp_wrt_exp_spec;
}.


#[global] Instance SVSTE :  SubstVarTheory exp exp (@var_f) := {
  size_open_var := size_exp_open_exp_wrt_exp_var;
  close_open := close_exp_wrt_exp_open_exp_wrt_exp;
  open_close := open_exp_wrt_exp_close_exp_wrt_exp;
  open_inj := open_exp_wrt_exp_inj;
  subst_open_var := subst_exp_open_exp_wrt_exp_var;
  subst_close_open := 
    subst_exp_wrt_exp_close_exp_wrt_exp_open_exp_wrt_exp;
  subst_intro := subst_exp_wrt_exp_intro;

}.


#[global] Opaque SVSTE.

#[global] Instance SSSTE : SubstSubstTheory exp exp := {
  subst_open := subst_exp_open_exp_wrt_exp;
  subst_subst := subst_exp_wrt_exp_subst_exp_wrt_exp;
}.

#[global] Opaque SSSTE.
