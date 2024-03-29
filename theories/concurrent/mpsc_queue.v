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

Record mpsc_queue `{!heapGS Σ} {unboxed : bool} := {
  mpsc_queue_make : val ;
  mpsc_queue_push : val ;
  mpsc_queue_pop : val ;

  mpsc_queue_name : Type ;
  #[global] mpsc_queue_name_eq_dec ::
    EqDecision mpsc_queue_name ;
  #[global] mpsc_queue_name_countable ::
    Countable mpsc_queue_name ;

  mpsc_queue_inv : val → mpsc_queue_name → namespace → iProp Σ ;
  mpsc_queue_model : val → mpsc_queue_name → list val → iProp Σ ;
  mpsc_queue_consumer : val → mpsc_queue_name → iProp Σ ;

  #[global] mpsc_queue_inv_persistent t γ ι ::
    Persistent (mpsc_queue_inv t γ ι) ;
  #[global] mpsc_queue_model_timeless t γ vs ::
    Timeless (mpsc_queue_model t γ vs) ;
  #[global] mpsc_queue_consumer_timeless t γ ::
    Timeless (mpsc_queue_consumer t γ) ;

  mpsc_queue_consumer_exclusive t γ :
    mpsc_queue_consumer t γ -∗
    mpsc_queue_consumer t γ -∗
    False ;

  mpsc_queue_make_spec ι :
    {{{ True }}}
      mpsc_queue_make #()
    {{{ t γ,
      RET t;
      mpsc_queue_inv t γ ι ∗
      mpsc_queue_model t γ [] ∗
      mpsc_queue_consumer t γ
    }}} ;

  mpsc_queue_push_spec t γ ι v :
    <<<
      mpsc_queue_inv t γ ι
    | ∀∀ vs, mpsc_queue_model t γ vs
    >>>
      mpsc_queue_push t v @ ↑ι
    <<<
      mpsc_queue_model t γ (v :: vs)
    | RET #(); True
    >>> ;

  mpsc_queue_pop_spec t γ ι :
    <<<
      mpsc_queue_inv t γ ι ∗
      mpsc_queue_consumer t γ
    | ∀∀ vs, mpsc_queue_model t γ vs
    >>>
      mpsc_queue_pop t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          mpsc_queue_model t γ []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          mpsc_queue_model t γ vs'
      end
    | RET o;
      mpsc_queue_consumer t γ
    >>> ;

  mpsc_queue_unboxed :
    if unboxed then ∀ t γ ι,
      mpsc_queue_inv t γ ι -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments mpsc_queue _ {_} _ : assert.
#[global] Arguments Build_mpsc_queue {_ _} _ {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ : assert.

Class MpscQueueOfMpmcQueueG Σ `{!heapGS Σ} := {
  #[local] mpsc_queue_of_mpmc_queue_G_consumer_G :: ExclG Σ unitO ;
}.

Definition mpsc_queue_of_mpmc_queue_Σ := #[
  excl_Σ unitO
].
Lemma subG_mpsc_queue_of_mpmc_queue_Σ Σ `{!heapGS Σ} :
  subG mpsc_queue_of_mpmc_queue_Σ Σ →
  MpscQueueOfMpmcQueueG Σ.
Proof.
  solve_inG.
Qed.

Program Coercion mpsc_queue_of_mpmc_queue
  `{mpsc_queue_of_mpmc_queue_G : MpscQueueOfMpmcQueueG Σ}
  {unboxed} (mpmc_queue : mpmc_queue Σ unboxed)
  : mpsc_queue Σ unboxed
:= {|
  mpsc_queue_make :=
    mpmc_queue.(mpmc_queue_make) ;
  mpsc_queue_push :=
    mpmc_queue.(mpmc_queue_push) ;
  mpsc_queue_pop :=
    mpmc_queue.(mpmc_queue_pop) ;

  mpsc_queue_name :=
    mpmc_queue.(mpmc_queue_name) * gname ;
  mpsc_queue_inv t γ ι :=
    mpmc_queue.(mpmc_queue_inv) t γ.1 ι ;
  mpsc_queue_model t γ :=
    mpmc_queue.(mpmc_queue_model) t γ.1 ;
  mpsc_queue_consumer _ γ :=
    excl γ.2 () ;
|}.
Next Obligation.
  intros. apply excl_exclusive.
Qed.
Next Obligation.
  iIntros "* _ HΦ".
  iMod excl_alloc as "(%γ_consumer & Hconsumer)".
  wp_apply (mpmc_queue_make_spec with "[//]"). iIntros "%t %γ_base (Hinv & Hmodel)".
  iApply ("HΦ" $! t (γ_base, γ_consumer)). iFrame.
Qed.
Next Obligation.
  intros. apply mpmc_queue_push_spec.
Qed.
Next Obligation.
  iIntros "* !> %Φ (Hinv & Hconsumer) HΦ".
  wp_apply (mpmc_queue_pop_spec with "Hinv").
  iApply (atomic_update_wand with "[Hconsumer] HΦ").
  iIntros "_ %v HΦ _". iApply "HΦ". done.
Qed.
Next Obligation.
  intros. destruct unboxed; last done.
  eauto using mpmc_queue.(mpmc_queue_unboxed).
Qed.
