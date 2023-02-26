From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.concurrent Require Export
  base.

Implicit Types v t : val.
Implicit Types vs : list val.

Record mpmc_stack `{!heapGS Σ} := {
  mpmc_stack_make : val ;
  mpmc_stack_push : val ;
  mpmc_stack_pop : val ;

  mpmc_stack_namespace : namespace ;
  mpmc_stack_inv : val → iProp Σ ;
  mpmc_stack_model : val → list val → iProp Σ ;

  mpmc_stack_inv_persistent t :
    Persistent (mpmc_stack_inv t) ;
  mpmc_stack_model_timeless t vs :
    Timeless (mpmc_stack_model t vs) ;

  mpmc_stack_make_spec :
    {{{ True }}}
      mpmc_stack_make #()
    {{{ t, RET t; mpmc_stack_inv t ∗ mpmc_stack_model t [] }}} ;

  mpmc_stack_push_spec t v :
    <<< mpmc_stack_inv t | ∀∀ vs, mpmc_stack_model t vs >>>
      mpmc_stack_push t v
      @ ↑ mpmc_stack_namespace
    <<< mpmc_stack_model t (v :: vs) | RET #(); True >>> ;

  mpmc_stack_pop_spec t :
    <<< mpmc_stack_inv t | ∀∀ vs, mpmc_stack_model t vs >>>
      mpmc_stack_pop t
      @ ↑ mpmc_stack_namespace
    <<< ∃∃ w,
      (⌜vs = [] ∧ w = NONEV⌝ ∗ mpmc_stack_model t []) ∨
      (∃ v vs', ⌜w = SOMEV v ∧ vs = v :: vs'⌝ ∗ mpmc_stack_model t vs') |
      RET w; True
    >>> ;
}.
#[global] Arguments mpmc_stack _ {_} : assert.
#[global] Arguments Build_mpmc_stack {_ _ _ _ _ _ _ _ _ _} _ _ _ : assert.
#[global] Existing Instance mpmc_stack_inv_persistent.
#[global] Existing Instance mpmc_stack_model_timeless.
