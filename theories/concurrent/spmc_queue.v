From caml5 Require Import
  prelude.
From caml5.base_logic Require Import
  lib.excl.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.concurrent Require Export
  base.
From caml5.concurrent Require Import
  mpmc_queue.

Implicit Types v t : val.
Implicit Types vs : list val.

Record spmc_queue `{!heapGS Σ} {unboxed : bool} := {
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

  spmc_queue_producer_exclusive t γ :
    spmc_queue_producer t γ -∗
    spmc_queue_producer t γ -∗
    False ;

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
      spmc_queue_push t v @ ↑ι
    <<<
      spmc_queue_model t γ (v :: vs) |
      RET #(); spmc_queue_producer t γ
    >>> ;

  spmc_queue_pop_spec t γ ι :
    <<<
      spmc_queue_inv t γ ι |
      ∀∀ vs, spmc_queue_model t γ vs
    >>>
      spmc_queue_pop t @ ↑ι
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ spmc_queue_model t γ []) ∨
      (∃ vs' v, ⌜vs = vs' ++ [v] ∧ o = SOMEV v⌝ ∗ spmc_queue_model t γ vs') |
      RET o; True
    >>> ;

  spmc_queue_unboxed :
    if unboxed then ∀ t γ ι,
      spmc_queue_inv t γ ι -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments spmc_queue _ {_} _ : assert.
#[global] Arguments Build_spmc_queue {_ _} _ {_ _ _ _ _ _ _ _ _ _ _} _ _ _ _ : assert.
#[global] Existing Instance spmc_queue_inv_persistent.
#[global] Existing Instance spmc_queue_model_timeless.
#[global] Existing Instance spmc_queue_producer_timeless.

Class SpmcQueueOfMpmcQueueG Σ `{!heapGS Σ} := {
  spmc_queue_of_mpmc_queue_G_producer_G : ExclG Σ unitO ;
}.
#[local] Existing Instance spmc_queue_of_mpmc_queue_G_producer_G.

Definition spmc_queue_of_mpmc_queue_Σ := #[
  excl_Σ unitO
].
Lemma subG_spmc_queue_of_mpmc_queue_Σ Σ `{!heapGS Σ} :
  subG spmc_queue_of_mpmc_queue_Σ Σ →
  SpmcQueueOfMpmcQueueG Σ.
Proof.
  solve_inG.
Qed.

Section spmc_queue_of_mpmc_queue.
  Context `{SpmcQueueOfMpmcQueueG Σ} {unboxed} (mpmc_queue : mpmc_queue Σ unboxed).

  Notation "γ .(base)" := γ.1
  ( at level 5
  ) : stdpp_scope.
  Notation "γ .(producer)" := γ.2
  ( at level 5
  ) : stdpp_scope.

  Program Definition spmc_queue_of_mpmc_queue : spmc_queue Σ unboxed := {|
    spmc_queue_make :=
      mpmc_queue.(mpmc_queue_make) ;
    spmc_queue_push :=
      mpmc_queue.(mpmc_queue_push) ;
    spmc_queue_pop :=
      mpmc_queue.(mpmc_queue_pop) ;

    spmc_queue_name :=
      mpmc_queue.(mpmc_queue_name) * gname ;
    spmc_queue_inv t γ ι :=
      mpmc_queue.(mpmc_queue_inv) t γ.(base) ι ;
    spmc_queue_model t γ :=
      mpmc_queue.(mpmc_queue_model) t γ.(base) ;
    spmc_queue_producer _ γ :=
      excl γ.(producer) () ;
  |}.
  Next Obligation.
    intros. apply excl_exclusive.
  Qed.
  Next Obligation.
    iIntros "%ι %Φ _ HΦ".
    iMod excl_alloc as "(%γ_producer & Hproducer)".
    wp_apply (mpmc_queue_make_spec with "[//]"). iIntros "%t %γ_base (Hinv & Hmodel)".
    iApply ("HΦ" $! t (γ_base, γ_producer)). iFrame.
  Qed.
  Next Obligation.
    iIntros "%t %γ %ι %v !> %Φ (Hinv & Hproducer) HΦ".
    wp_apply (mpmc_queue_push_spec with "Hinv").
    iApply (atomic_update_wand with "[Hproducer] HΦ").
    iIntros "_ HΦ _". iApply "HΦ". done.
  Qed.
  Next Obligation.
    intros. apply mpmc_queue_pop_spec.
  Qed.
  Next Obligation.
    destruct unboxed; last done. eauto using mpmc_queue.(mpmc_queue_unboxed).
  Qed.
End spmc_queue_of_mpmc_queue.
