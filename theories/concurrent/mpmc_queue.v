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

  mpmc_queue_name : Type ;
  mpmc_queue_inv : val → mpmc_queue_name → namespace → iProp Σ ;
  mpmc_queue_model : val → mpmc_queue_name → list val → iProp Σ ;

  mpmc_queue_inv_persistent t γ ι :
    Persistent (mpmc_queue_inv t γ ι) ;
  mpmc_queue_model_timeless t γ vs :
    Timeless (mpmc_queue_model t γ vs) ;

  mpmc_queue_make_spec ι :
    {{{ True }}}
      mpmc_queue_make #()
    {{{ t γ, RET t; mpmc_queue_inv t γ ι ∗ mpmc_queue_model t γ [] }}} ;

  mpmc_queue_push_spec t γ ι v :
    <<< mpmc_queue_inv t γ ι | ∀∀ vs, mpmc_queue_model t γ vs >>>
      mpmc_queue_push t v
      @ ↑ ι
    <<< mpmc_queue_model t γ (v :: vs) | RET #(); True >>> ;

  mpmc_queue_pop_spec t γ ι :
    <<< mpmc_queue_inv t γ ι | ∀∀ vs, mpmc_queue_model t γ vs >>>
      mpmc_queue_pop t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ mpmc_queue_model t γ []) ∨
      (∃ vs' v, ⌜vs = vs' ++ [v] ∧ o = SOMEV v⌝ ∗ mpmc_queue_model t γ vs') |
      RET o; True
    >>> ;
}.
#[global] Arguments mpmc_queue _ {_} : assert.
#[global] Arguments Build_mpmc_queue {_ _ _ _ _ _ _ _ _ _} _ _ _ : assert.
#[global] Existing Instance mpmc_queue_inv_persistent.
#[global] Existing Instance mpmc_queue_model_timeless.
