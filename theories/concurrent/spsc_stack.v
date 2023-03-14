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
  mpmc_stack
  spmc_stack
  mpsc_stack.

Implicit Types v t : val.
Implicit Types vs : list val.

Record spsc_stack `{!heapGS Σ} := {
  spsc_stack_make : val ;
  spsc_stack_push : val ;
  spsc_stack_pop : val ;

  spsc_stack_name : Type ;
  spsc_stack_inv : val → spsc_stack_name → namespace → iProp Σ ;
  spsc_stack_model : val → spsc_stack_name → list val → iProp Σ ;
  spsc_stack_producer : val → spsc_stack_name → iProp Σ ;
  spsc_stack_consumer : val → spsc_stack_name → iProp Σ ;

  spsc_stack_inv_persistent t γ ι :
    Persistent (spsc_stack_inv t γ ι) ;
  spsc_stack_model_timeless t γ vs :
    Timeless (spsc_stack_model t γ vs) ;
  spsc_stack_producer_timeless t γ :
    Timeless (spsc_stack_producer t γ) ;
  spsc_stack_consumer_timeless t γ :
    Timeless (spsc_stack_consumer t γ) ;

  spsc_stack_producer_exclusive t γ :
    spsc_stack_producer t γ -∗
    spsc_stack_producer t γ -∗
    False ;
  spsc_stack_consumer_exclusive t γ :
    spsc_stack_consumer t γ -∗
    spsc_stack_consumer t γ -∗
    False ;

  spsc_stack_make_spec ι :
    {{{ True }}}
      spsc_stack_make #()
    {{{ t γ,
      RET t;
      spsc_stack_inv t γ ι ∗
      spsc_stack_model t γ [] ∗
      spsc_stack_producer t γ ∗
      spsc_stack_consumer t γ
    }}} ;

  spsc_stack_push_spec t γ ι v :
    <<<
      spsc_stack_inv t γ ι ∗
      spsc_stack_producer t γ |
      ∀∀ vs, spsc_stack_model t γ vs
    >>>
      spsc_stack_push t v
      @ ↑ ι
    <<<
      spsc_stack_model t γ (v :: vs) |
      RET #(); spsc_stack_producer t γ
    >>> ;

  spsc_stack_pop_spec t γ ι :
    <<<
      spsc_stack_inv t γ ι ∗
      spsc_stack_consumer t γ |
      ∀∀ vs, spsc_stack_model t γ vs
    >>>
      spsc_stack_pop t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ spsc_stack_model t γ []) ∨
      (∃ v vs', ⌜vs = v :: vs' ∧ o = SOMEV v⌝ ∗ spsc_stack_model t γ vs') |
      RET o; spsc_stack_consumer t γ
    >>> ;
}.
#[global] Arguments spsc_stack _ {_} : assert.
#[global] Arguments Build_spsc_stack {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ : assert.
#[global] Existing Instance spsc_stack_inv_persistent.
#[global] Existing Instance spsc_stack_model_timeless.
#[global] Existing Instance spsc_stack_producer_timeless.
#[global] Existing Instance spsc_stack_consumer_timeless.

Class SpscStackOfSpmcStackG Σ `{!heapGS Σ} := {
  spsc_stack_of_spmc_stack_G_consumer_G : ExclG Σ unitO ;
}.
#[local] Existing Instance spsc_stack_of_spmc_stack_G_consumer_G.

Definition spsc_stack_of_spmc_stack_Σ := #[
  excl_Σ unitO
].
Lemma subG_spsc_stack_of_spmc_stack_Σ Σ `{!heapGS Σ} :
  subG spsc_stack_of_spmc_stack_Σ Σ →
  SpscStackOfSpmcStackG Σ.
Proof.
  solve_inG.
Qed.

Section spsc_stack_of_spmc_stack.
  Context `{SpscStackOfSpmcStackG Σ} (spmc_stack : spmc_stack Σ).

  Notation "γ .(base)" := γ.1
  ( at level 5
  ) : stdpp_scope.
  Notation "γ .(consumer)" := γ.2
  ( at level 5
  ) : stdpp_scope.

  Program Definition spsc_stack_of_spmc_stack := {|
    spsc_stack_make :=
      spmc_stack.(spmc_stack_make) ;
    spsc_stack_push :=
      spmc_stack.(spmc_stack_push) ;
    spsc_stack_pop :=
      spmc_stack.(spmc_stack_pop) ;

    spsc_stack_name :=
      spmc_stack.(spmc_stack_name) * gname ;
    spsc_stack_inv t γ ι :=
      spmc_stack.(spmc_stack_inv) t γ.(base) ι ;
    spsc_stack_model t γ :=
      spmc_stack.(spmc_stack_model) t γ.(base) ;
    spsc_stack_producer t γ :=
      spmc_stack.(spmc_stack_producer) t γ.(base) ;
    spsc_stack_consumer _ γ :=
      excl γ.(consumer) () ;
  |}.
  Next Obligation.
    intros. apply spmc_stack_producer_exclusive.
  Qed.
  Next Obligation.
    intros. apply excl_exclusive.
  Qed.
  Next Obligation.
    iIntros "%ι %Φ _ HΦ".
    iMod excl_alloc as "(%γ_consumer & Hconsumer)".
    wp_apply (spmc_stack_make_spec with "[//]"). iIntros "%t %γ_base (Hinv & Hmodel & Hproducer)".
    iApply ("HΦ" $! t (γ_base, γ_consumer)). iFrame.
  Qed.
  Next Obligation.
    intros. apply spmc_stack_push_spec.
  Qed.
  Next Obligation.
    iIntros "%t %γ %ι !> %Φ (Hinv & Hconsumer) HΦ".
    wp_apply (spmc_stack_pop_spec with "Hinv").
    iApply (atomic_update_wand with "[Hconsumer] HΦ").
    iIntros "_ %v HΦ _". iApply "HΦ". done.
  Qed.
End spsc_stack_of_spmc_stack.

Class SpscStackOfMpscStackG Σ `{!heapGS Σ} := {
  spsc_stack_of_mpsc_stack_G_producer_G : ExclG Σ unitO ;
}.
#[local] Existing Instance spsc_stack_of_mpsc_stack_G_producer_G.

Definition spsc_stack_of_mpsc_stack_Σ := #[
  excl_Σ unitO
].
Lemma subG_spsc_stack_of_mpsc_stack_Σ Σ `{!heapGS Σ} :
  subG spsc_stack_of_mpsc_stack_Σ Σ →
  SpscStackOfMpscStackG Σ.
Proof.
  solve_inG.
Qed.

Section spsc_stack_of_mpsc_stack.
  Context `{SpscStackOfMpscStackG Σ} (mpsc_stack : mpsc_stack Σ).

  Notation "γ .(base)" := γ.1
  ( at level 5
  ) : stdpp_scope.
  Notation "γ .(producer)" := γ.2
  ( at level 5
  ) : stdpp_scope.

  Program Definition spsc_stack_of_mpsc_stack := {|
    spsc_stack_make :=
      mpsc_stack.(mpsc_stack_make) ;
    spsc_stack_push :=
      mpsc_stack.(mpsc_stack_push) ;
    spsc_stack_pop :=
      mpsc_stack.(mpsc_stack_pop) ;

    spsc_stack_name :=
      mpsc_stack.(mpsc_stack_name) * gname ;
    spsc_stack_inv t γ ι :=
      mpsc_stack.(mpsc_stack_inv) t γ.(base) ι ;
    spsc_stack_model t γ :=
      mpsc_stack.(mpsc_stack_model) t γ.(base) ;
    spsc_stack_producer _ γ :=
      excl γ.(producer) () ;
    spsc_stack_consumer t γ :=
      mpsc_stack.(mpsc_stack_consumer) t γ.(base) ;
  |}.
  Next Obligation.
    intros. apply excl_exclusive.
  Qed.
  Next Obligation.
    intros. apply mpsc_stack_consumer_exclusive.
  Qed.
  Next Obligation.
    iIntros "%ι %Φ _ HΦ".
    iMod excl_alloc as "(%γ_producer & Hproducer)".
    wp_apply (mpsc_stack_make_spec with "[//]"). iIntros "%t %γ_base (Hinv & Hmodel & Hconsumer)".
    iApply ("HΦ" $! t (γ_base, γ_producer)). iFrame.
  Qed.
  Next Obligation.
    iIntros "%t %γ %ι %v !> %Φ (Hinv & Hproducer) HΦ".
    wp_apply (mpsc_stack_push_spec with "Hinv").
    iApply (atomic_update_wand with "[Hproducer] HΦ").
    iIntros "_ HΦ _". iApply "HΦ". done.
  Qed.
  Next Obligation.
    intros. apply mpsc_stack_pop_spec.
  Qed.
End spsc_stack_of_mpsc_stack.

Class SpscStackOfMpmcStackG Σ `{!heapGS Σ} := {
  spsc_stack_of_mpmc_stack_G_mpmc_stack_G : SpmcStackOfMpmcStackG Σ ;
  spsc_stack_of_mpmc_stack_G_spmc_stack_G : SpscStackOfSpmcStackG Σ ;
}.
#[local] Existing Instance spsc_stack_of_mpmc_stack_G_mpmc_stack_G.
#[local] Existing Instance spsc_stack_of_mpmc_stack_G_spmc_stack_G.

Definition spsc_stack_of_mpmc_stack_Σ := #[
  spmc_stack_of_mpmc_stack_Σ ;
  spsc_stack_of_spmc_stack_Σ
].
Lemma subG_spsc_stack_of_mpmc_stack_Σ Σ `{!heapGS Σ} :
  subG spsc_stack_of_mpmc_stack_Σ Σ →
  SpscStackOfMpmcStackG Σ.
Proof.
  pose subG_spmc_stack_of_mpmc_stack_Σ.
  pose subG_spsc_stack_of_spmc_stack_Σ.
  solve_inG.
Qed.

Definition spsc_stack_of_mpmc_stack `{SpscStackOfMpmcStackG Σ} mpmc_stack :=
  spsc_stack_of_spmc_stack (spmc_stack_of_mpmc_stack mpmc_stack).
