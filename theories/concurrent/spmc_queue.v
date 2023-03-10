From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.concurrent Require Export
  base.
From caml5.concurrent Require Import
  mpmc_queue.

Implicit Types v t : val.
Implicit Types vs : list val.

Record spmc_queue `{!heapGS Σ} := {
  spmc_queue_make : val ;
  spmc_queue_push : val ;
  spmc_queue_pop : val ;

  spmc_queue_name : Type ;
  spmc_queue_inv : val → spmc_queue_name → namespace → iProp Σ ;
  spmc_queue_model : val → spmc_queue_name → list val → iProp Σ ;
  spmc_queue_producer : val → spmc_queue_name → iProp Σ ;

  spmc_queue_inv_persistent t γ ι :
    Persistent (spmc_queue_inv t γ ι) ;
  spmc_queue_model_timeless t γ vs :
    Timeless (spmc_queue_model t γ vs) ;
  spmc_queue_producer_timeless t γ :
    Timeless (spmc_queue_producer t γ) ;

  spmc_queue_make_spec ι :
    {{{ True }}}
      spmc_queue_make #()
    {{{ t γ,
      RET t;
      spmc_queue_inv t γ ι ∗
      spmc_queue_model t γ [] ∗
      spmc_queue_producer t γ
    }}} ;

  spmc_queue_push_spec t γ ι v :
    <<<
      spmc_queue_inv t γ ι ∗
      spmc_queue_producer t γ |
      ∀∀ vs, spmc_queue_model t γ vs
    >>>
      spmc_queue_push t v
      @ ↑ ι
    <<<
      spmc_queue_model t γ (v :: vs) |
      RET #(); spmc_queue_producer t γ
    >>> ;

  spmc_queue_pop_spec t γ ι :
    <<<
      spmc_queue_inv t γ ι |
      ∀∀ vs, spmc_queue_model t γ vs
    >>>
      spmc_queue_pop t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ spmc_queue_model t γ []) ∨
      (∃ vs' v, ⌜vs = vs' ++ [v] ∧ o = SOMEV v⌝ ∗ spmc_queue_model t γ vs') |
      RET o; True
    >>> ;
}.
#[global] Arguments spmc_queue _ {_} : assert.
#[global] Arguments Build_spmc_queue {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _ : assert.
#[global] Existing Instance spmc_queue_inv_persistent.
#[global] Existing Instance spmc_queue_model_timeless.
#[global] Existing Instance spmc_queue_producer_timeless.

Program Definition spmc_queue_of_mpmc_queue `{!heapGS Σ} mpmc_queue := {|
  spmc_queue_make := mpmc_queue.(mpmc_queue_make) ;
  spmc_queue_push := mpmc_queue.(mpmc_queue_push) ;
  spmc_queue_pop := mpmc_queue.(mpmc_queue_pop) ;

  spmc_queue_name := mpmc_queue.(mpmc_queue_name) ;
  spmc_queue_inv := mpmc_queue.(mpmc_queue_inv) ;
  spmc_queue_model := mpmc_queue.(mpmc_queue_model) ;
  spmc_queue_producer _ _ := True%I ;
|}.
Next Obligation.
  intros.
  setoid_rewrite (@right_id _ equiv True%I); last apply _.
  apply mpmc_queue_make_spec.
Qed.
Next Obligation.
  intros.
  rewrite /atomic_triple. setoid_rewrite (@right_id _ equiv True%I); last apply _.
  apply mpmc_queue_push_spec.
Qed.
Next Obligation.
  intros. apply mpmc_queue_pop_spec.
Qed.
