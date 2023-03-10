From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.concurrent Require Export
  base.
From caml5.concurrent Require Import
  mpmc_stack.

Implicit Types v t : val.
Implicit Types vs : list val.

Record spmc_stack `{!heapGS Σ} := {
  spmc_stack_make : val ;
  spmc_stack_push : val ;
  spmc_stack_pop : val ;

  spmc_stack_name : Type ;
  spmc_stack_inv : val → spmc_stack_name → namespace → iProp Σ ;
  spmc_stack_model : val → spmc_stack_name → list val → iProp Σ ;
  spmc_stack_producer : val → spmc_stack_name → iProp Σ ;

  spmc_stack_inv_persistent t γ ι :
    Persistent (spmc_stack_inv t γ ι) ;
  spmc_stack_model_timeless t γ vs :
    Timeless (spmc_stack_model t γ vs) ;
  spmc_stack_producer_timeless t γ :
    Timeless (spmc_stack_producer t γ) ;

  spmc_stack_make_spec ι :
    {{{ True }}}
      spmc_stack_make #()
    {{{ t γ,
      RET t;
      spmc_stack_inv t γ ι ∗
      spmc_stack_model t γ [] ∗
      spmc_stack_producer t γ
    }}} ;

  spmc_stack_push_spec t γ ι v :
    <<<
      spmc_stack_inv t γ ι ∗
      spmc_stack_producer t γ |
      ∀∀ vs, spmc_stack_model t γ vs
    >>>
      spmc_stack_push t v
      @ ↑ ι
    <<<
      spmc_stack_model t γ (v :: vs) |
      RET #(); spmc_stack_producer t γ
    >>> ;

  spmc_stack_pop_spec t γ ι :
    <<<
      spmc_stack_inv t γ ι |
      ∀∀ vs, spmc_stack_model t γ vs
    >>>
      spmc_stack_pop t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ spmc_stack_model t γ []) ∨
      (∃ v vs', ⌜vs = v :: vs' ∧ o = SOMEV v⌝ ∗ spmc_stack_model t γ vs') |
      RET o; True
    >>> ;
}.
#[global] Arguments spmc_stack _ {_} : assert.
#[global] Arguments Build_spmc_stack {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _ : assert.
#[global] Existing Instance spmc_stack_inv_persistent.
#[global] Existing Instance spmc_stack_model_timeless.
#[global] Existing Instance spmc_stack_producer_timeless.

Program Definition spmc_stack_of_mpmc_stack `{!heapGS Σ} mpmc_stack := {|
  spmc_stack_make := mpmc_stack.(mpmc_stack_make) ;
  spmc_stack_push := mpmc_stack.(mpmc_stack_push) ;
  spmc_stack_pop := mpmc_stack.(mpmc_stack_pop) ;

  spmc_stack_name := mpmc_stack.(mpmc_stack_name) ;
  spmc_stack_inv := mpmc_stack.(mpmc_stack_inv) ;
  spmc_stack_model := mpmc_stack.(mpmc_stack_model) ;
  spmc_stack_producer _ _ := True%I ;
|}.
Next Obligation.
  intros.
  setoid_rewrite (@right_id _ equiv True%I); last apply _.
  apply mpmc_stack_make_spec.
Qed.
Next Obligation.
  intros.
  rewrite /atomic_triple. setoid_rewrite (@right_id _ equiv True%I); last apply _.
  apply mpmc_stack_push_spec.
Qed.
Next Obligation.
  intros. apply mpmc_stack_pop_spec.
Qed.
