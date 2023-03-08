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

  mpmc_stack_inv : val → namespace → iProp Σ ;
  mpmc_stack_model : val → list val → iProp Σ ;

  mpmc_stack_inv_persistent t ι :
    Persistent (mpmc_stack_inv t ι) ;
  mpmc_stack_model_timeless t vs :
    Timeless (mpmc_stack_model t vs) ;

  mpmc_stack_make_spec ι :
    {{{ True }}}
      mpmc_stack_make #()
    {{{ t, RET t; mpmc_stack_inv t ι ∗ mpmc_stack_model t [] }}} ;

  mpmc_stack_push_spec t ι v :
    <<< mpmc_stack_inv t ι | ∀∀ vs, mpmc_stack_model t vs >>>
      mpmc_stack_push t v
      @ ↑ ι
    <<< mpmc_stack_model t (v :: vs) | RET #(); True >>> ;

  mpmc_stack_pop_spec t ι :
    <<< mpmc_stack_inv t ι | ∀∀ vs, mpmc_stack_model t vs >>>
      mpmc_stack_pop t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ mpmc_stack_model t []) ∨
      (∃ v vs', ⌜vs = v :: vs' ∧ o = SOMEV v⌝ ∗ mpmc_stack_model t vs') |
      RET o; True
    >>> ;
}.
#[global] Arguments mpmc_stack _ {_} : assert.
#[global] Arguments Build_mpmc_stack {_ _ _ _ _ _ _ _ _} _ _ _ : assert.
#[global] Existing Instance mpmc_stack_inv_persistent.
#[global] Existing Instance mpmc_stack_model_timeless.
