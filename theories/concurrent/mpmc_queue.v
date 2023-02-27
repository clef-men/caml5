From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.concurrent Require Export
  base.

Implicit Types v w t : val.
Implicit Types vs : list val.

Record mpmc_queue `{!heapGS Σ} := {
  mpmc_queue_make : val ;
  mpmc_queue_push : val ;
  mpmc_queue_pop : val ;

  mpmc_queue_namespace : namespace ;
  mpmc_queue_inv : val → iProp Σ ;
  mpmc_queue_model : val → list val → iProp Σ ;

  mpmc_queue_inv_persistent t :
    Persistent (mpmc_queue_inv t) ;
  mpmc_queue_model_timeless t vs :
    Timeless (mpmc_queue_model t vs) ;

  mpmc_queue_make_spec :
    {{{ True }}}
      mpmc_queue_make #()
    {{{ t, RET t; mpmc_queue_inv t ∗ mpmc_queue_model t [] }}} ;

  mpmc_queue_push_spec t v :
    <<< mpmc_queue_inv t | ∀∀ vs, mpmc_queue_model t vs >>>
      mpmc_queue_push t v
      @ ↑ mpmc_queue_namespace
    <<< mpmc_queue_model t (v :: vs) | RET #(); True >>> ;

  mpmc_queue_pop_spec t :
    <<< mpmc_queue_inv t | ∀∀ vs, mpmc_queue_model t vs >>>
      mpmc_queue_pop t
      @ ↑ mpmc_queue_namespace
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ mpmc_queue_model t []) ∨
      (∃ vs' v, ⌜vs = vs' ++ [v] ∧ o = SOMEV v⌝ ∗ mpmc_queue_model t vs') |
      RET o; True
    >>> ;
}.
#[global] Arguments mpmc_queue _ {_} : assert.
#[global] Arguments Build_mpmc_queue {_ _ _ _ _ _ _ _ _ _} _ _ _ : assert.
#[global] Existing Instance mpmc_queue_inv_persistent.
#[global] Existing Instance mpmc_queue_model_timeless.
