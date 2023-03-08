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

  mpmc_queue_inv : val → namespace → iProp Σ ;
  mpmc_queue_model : val → list val → iProp Σ ;

  mpmc_queue_inv_persistent t ι :
    Persistent (mpmc_queue_inv t ι) ;
  mpmc_queue_model_timeless t vs :
    Timeless (mpmc_queue_model t vs) ;

  mpmc_queue_make_spec ι :
    {{{ True }}}
      mpmc_queue_make #()
    {{{ t, RET t; mpmc_queue_inv t ι ∗ mpmc_queue_model t [] }}} ;

  mpmc_queue_push_spec t ι v :
    <<< mpmc_queue_inv t ι | ∀∀ vs, mpmc_queue_model t vs >>>
      mpmc_queue_push t v
      @ ↑ ι
    <<< mpmc_queue_model t (v :: vs) | RET #(); True >>> ;

  mpmc_queue_pop_spec t ι :
    <<< mpmc_queue_inv t ι | ∀∀ vs, mpmc_queue_model t vs >>>
      mpmc_queue_pop t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ mpmc_queue_model t []) ∨
      (∃ vs' v, ⌜vs = vs' ++ [v] ∧ o = SOMEV v⌝ ∗ mpmc_queue_model t vs') |
      RET o; True
    >>> ;
}.
#[global] Arguments mpmc_queue _ {_} : assert.
#[global] Arguments Build_mpmc_queue {_ _ _ _ _ _ _ _ _} _ _ _ : assert.
#[global] Existing Instance mpmc_queue_inv_persistent.
#[global] Existing Instance mpmc_queue_model_timeless.
