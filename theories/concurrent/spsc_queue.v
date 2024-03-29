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
  mpmc_queue
  spmc_queue
  mpsc_queue.

Implicit Types v t : val.
Implicit Types vs : list val.

Record spsc_queue `{!heapGS Σ} {unboxed : bool} := {
  spsc_queue_make : val ;
  spsc_queue_push : val ;
  spsc_queue_pop : val ;

  spsc_queue_name : Type ;
  #[global] spsc_queue_name_eq_dec ::
    EqDecision spsc_queue_name ;
  #[global] spsc_queue_name_countable ::
    Countable spsc_queue_name ;

  spsc_queue_inv : val → spsc_queue_name → namespace → iProp Σ ;
  spsc_queue_model : val → spsc_queue_name → list val → iProp Σ ;
  spsc_queue_producer : val → spsc_queue_name → iProp Σ ;
  spsc_queue_consumer : val → spsc_queue_name → iProp Σ ;

  #[global] spsc_queue_inv_persistent t γ ι ::
    Persistent (spsc_queue_inv t γ ι) ;
  #[global] spsc_queue_model_timeless t γ vs ::
    Timeless (spsc_queue_model t γ vs) ;
  #[global] spsc_queue_producer_timeless t γ ::
    Timeless (spsc_queue_producer t γ) ;
  #[global] spsc_queue_consumer_timeless t γ ::
    Timeless (spsc_queue_consumer t γ) ;

  spsc_queue_producer_exclusive t γ :
    spsc_queue_producer t γ -∗
    spsc_queue_producer t γ -∗
    False ;
  spsc_queue_consumer_exclusive t γ :
    spsc_queue_consumer t γ -∗
    spsc_queue_consumer t γ -∗
    False ;

  spsc_queue_make_spec ι :
    {{{ True }}}
      spsc_queue_make #()
    {{{ t γ,
      RET t;
      spsc_queue_inv t γ ι ∗
      spsc_queue_model t γ [] ∗
      spsc_queue_producer t γ ∗
      spsc_queue_consumer t γ
    }}} ;

  spsc_queue_push_spec t γ ι v :
    <<<
      spsc_queue_inv t γ ι ∗
      spsc_queue_producer t γ
    | ∀∀ vs, spsc_queue_model t γ vs
    >>>
      spsc_queue_push t v @ ↑ι
    <<<
      spsc_queue_model t γ (v :: vs)
    | RET #();
      spsc_queue_producer t γ
    >>> ;

  spsc_queue_pop_spec t γ ι :
    <<<
      spsc_queue_inv t γ ι ∗
      spsc_queue_consumer t γ
    | ∀∀ vs, spsc_queue_model t γ vs
    >>>
      spsc_queue_pop t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          spsc_queue_model t γ []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          spsc_queue_model t γ vs'
      end
    | RET o;
      spsc_queue_consumer t γ
    >>> ;

  spsc_queue_unboxed :
    if unboxed then ∀ t γ ι,
      spsc_queue_inv t γ ι -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments spsc_queue _ {_} _ : assert.
#[global] Arguments Build_spsc_queue {_ _} _ {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ : assert.

Class SpscQueueOfSpmcQueueG Σ `{!heapGS Σ} := {
  #[local] spsc_queue_of_spmc_queue_G_consumer_G :: ExclG Σ unitO ;
}.

Definition spsc_queue_of_spmc_queue_Σ := #[
  excl_Σ unitO
].
Lemma subG_spsc_queue_of_spmc_queue_Σ Σ `{!heapGS Σ} :
  subG spsc_queue_of_spmc_queue_Σ Σ →
  SpscQueueOfSpmcQueueG Σ.
Proof.
  solve_inG.
Qed.

Program Coercion spsc_queue_of_spmc_queue
  `{spsc_queue_of_spmc_queue_G : SpscQueueOfSpmcQueueG Σ}
  {unboxed} (spmc_queue : spmc_queue Σ unboxed)
  : spsc_queue Σ unboxed
:= {|
  spsc_queue_make :=
    spmc_queue.(spmc_queue_make) ;
  spsc_queue_push :=
    spmc_queue.(spmc_queue_push) ;
  spsc_queue_pop :=
    spmc_queue.(spmc_queue_pop) ;

  spsc_queue_name :=
    spmc_queue.(spmc_queue_name) * gname ;
  spsc_queue_inv t γ ι :=
    spmc_queue.(spmc_queue_inv) t γ.1 ι ;
  spsc_queue_model t γ :=
    spmc_queue.(spmc_queue_model) t γ.1 ;
  spsc_queue_producer t γ :=
    spmc_queue.(spmc_queue_producer) t γ.1 ;
  spsc_queue_consumer _ γ :=
    excl γ.2 () ;
|}.
Next Obligation.
  intros. apply spmc_queue_producer_exclusive.
Qed.
Next Obligation.
  intros. apply excl_exclusive.
Qed.
Next Obligation.
  iIntros "* _ HΦ".
  iMod excl_alloc as "(%γ_consumer & Hconsumer)".
  wp_apply (spmc_queue_make_spec with "[//]"). iIntros "%t %γ_base (Hinv & Hmodel & Hproducer)".
  iApply ("HΦ" $! t (γ_base, γ_consumer)). iFrame.
Qed.
Next Obligation.
  intros. apply spmc_queue_push_spec.
Qed.
Next Obligation.
  iIntros "* !> %Φ (Hinv & Hconsumer) HΦ".
  wp_apply (spmc_queue_pop_spec with "Hinv").
  iApply (atomic_update_wand with "[Hconsumer] HΦ").
  iIntros "_ %v HΦ _". iApply "HΦ". done.
Qed.
Next Obligation.
  intros. destruct unboxed; last done.
  eauto using spmc_queue.(spmc_queue_unboxed).
Qed.

Class SpscQueueOfMpscQueueG Σ `{!heapGS Σ} := {
  #[local] spsc_queue_of_mpsc_queue_G_producer_G :: ExclG Σ unitO ;
}.

Definition spsc_queue_of_mpsc_queue_Σ := #[
  excl_Σ unitO
].
Lemma subG_spsc_queue_of_mpsc_queue_Σ Σ `{!heapGS Σ} :
  subG spsc_queue_of_mpsc_queue_Σ Σ →
  SpscQueueOfMpscQueueG Σ.
Proof.
  solve_inG.
Qed.

Program Coercion spsc_queue_of_mpsc_queue
  `{spsc_queue_of_mpsc_queue_G : SpscQueueOfMpscQueueG Σ}
  {unboxed} (mpsc_queue : mpsc_queue Σ unboxed)
  : spsc_queue Σ unboxed
:= {|
  spsc_queue_make :=
    mpsc_queue.(mpsc_queue_make) ;
  spsc_queue_push :=
    mpsc_queue.(mpsc_queue_push) ;
  spsc_queue_pop :=
    mpsc_queue.(mpsc_queue_pop) ;

  spsc_queue_name :=
    mpsc_queue.(mpsc_queue_name) * gname ;
  spsc_queue_inv t γ ι :=
    mpsc_queue.(mpsc_queue_inv) t γ.1 ι ;
  spsc_queue_model t γ :=
    mpsc_queue.(mpsc_queue_model) t γ.1 ;
  spsc_queue_producer _ γ :=
    excl γ.2 () ;
  spsc_queue_consumer t γ :=
    mpsc_queue.(mpsc_queue_consumer) t γ.1 ;
|}.
Next Obligation.
  intros. apply excl_exclusive.
Qed.
Next Obligation.
  intros. apply mpsc_queue_consumer_exclusive.
Qed.
Next Obligation.
  iIntros "* _ HΦ".
  iMod excl_alloc as "(%γ_producer & Hproducer)".
  wp_apply (mpsc_queue_make_spec with "[//]"). iIntros "%t %γ_base (Hinv & Hmodel & Hconsumer)".
  iApply ("HΦ" $! t (γ_base, γ_producer)). iFrame.
Qed.
Next Obligation.
  iIntros "* !> %Φ (Hinv & Hproducer) HΦ".
  wp_apply (mpsc_queue_push_spec with "Hinv").
  iApply (atomic_update_wand with "[Hproducer] HΦ").
  iIntros "_ HΦ _". iApply "HΦ". done.
Qed.
Next Obligation.
  intros. apply mpsc_queue_pop_spec.
Qed.
Next Obligation.
  intros. destruct unboxed; last done.
  eauto using mpsc_queue.(mpsc_queue_unboxed).
Qed.

Class SpscQueueOfMpmcQueueG Σ `{!heapGS Σ} := {
  #[local] spsc_queue_of_mpmc_queue_G_mpmc_queue_G :: SpmcQueueOfMpmcQueueG Σ ;
  #[local] spsc_queue_of_mpmc_queue_G_spmc_queue_G :: SpscQueueOfSpmcQueueG Σ ;
}.

Definition spsc_queue_of_mpmc_queue_Σ := #[
  spmc_queue_of_mpmc_queue_Σ ;
  spsc_queue_of_spmc_queue_Σ
].
Lemma subG_spsc_queue_of_mpmc_queue_Σ Σ `{!heapGS Σ} :
  subG spsc_queue_of_mpmc_queue_Σ Σ →
  SpscQueueOfMpmcQueueG Σ.
Proof.
  pose subG_spmc_queue_of_mpmc_queue_Σ.
  pose subG_spsc_queue_of_spmc_queue_Σ.
  solve_inG.
Qed.

Coercion spsc_queue_of_mpmc_queue
  `{spsc_queue_of_mpmc_queue_G : SpscQueueOfMpmcQueueG Σ}
  {unboxed} {mpmc_queue : mpmc_queue Σ unboxed}
:=
  spsc_queue_of_spmc_queue (spmc_queue_of_mpmc_queue mpmc_queue).
