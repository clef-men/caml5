From caml5 Require Import
  prelude.
From caml5.base_logic Require Import
  lib.auth_excl.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Import
  queue.
From caml5.concurrent Require Export
  base.
From caml5.concurrent Require Import
  mutex
  mpmc_queue.

Class BlockingQueueGpre Σ `{!heapGS Σ} := {
  #[local] blocking_queue_Gpre_model_G :: AuthExclG Σ (leibnizO (list val)) ;
}.

Class BlockingQueueG Σ `{!heapGS Σ} := {
  #[local] blocking_queue_G_Gpre :: BlockingQueueGpre Σ ;
  blocking_queue_G_queue : queue Σ false ;
  blocking_queue_G_mutex : mutex Σ false ;
}.

Definition blocking_queue_Σ := #[
  auth_excl_Σ (leibnizO (list val))
].
#[global] Instance subG_blocking_queue_Σ Σ `{!heapGS Σ} :
  subG blocking_queue_Σ Σ →
  BlockingQueueGpre Σ.
Proof.
  solve_inG.
Qed.

Section blocking_queue_G.
  Context `{blocking_queue_G : BlockingQueueG Σ}.
  Implicit Types v t : val.
  Implicit Types vs : list val.

  Let queue := blocking_queue_G.(blocking_queue_G_queue).
  Let mutex := blocking_queue_G.(blocking_queue_G_mutex).

  Notation "t '.(queue)'" := t.1%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(mutex)'" := t.2%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(queue)'" := t.1%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(mutex)'" := t.2%E
  ( at level 5
  ) : expr_scope.

  Definition blocking_queue_make : val :=
    λ: <>,
      let: "q" := queue.(queue_make) #() in
      let: "mtx" := mutex.(mutex_make) #() in
      ("q", "mtx").

  Definition blocking_queue_push : val :=
    λ: "t" "v",
      mutex.(mutex_protect) "t".(mutex) (λ: <>,
        queue.(queue_push) "t".(queue) "v"
      ).

  Definition blocking_queue_pop : val :=
    λ: "t",
      mutex.(mutex_protect) "t".(mutex) (λ: <>,
        queue.(queue_pop) "t".(queue)
      ).

  #[local] Definition blocking_queue_inv_inner γ q : iProp Σ :=
    ∃ vs,
    queue.(queue_model) q vs ∗
    auth_excl_frag γ vs.
  Definition blocking_queue_inv t γ : iProp Σ :=
    ∃ q mtx,
    ⌜t = (q, mtx)%V⌝ ∗
    mutex.(mutex_inv) mtx (blocking_queue_inv_inner γ q).

  Definition blocking_queue_model t γ vs :=
    auth_excl_auth γ (DfracOwn 1) vs.

  #[global] Instance blocking_queue_inv_persistent t γ :
    Persistent (blocking_queue_inv t γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance blocking_queue_model_timeless t γ vs :
    Timeless (blocking_queue_model t γ vs).
  Proof.
    apply _.
  Qed.

  Lemma blocking_queue_make_spec :
    {{{ True }}}
      blocking_queue_make #()
    {{{ t γ,
      RET t;
      blocking_queue_inv t γ ∗
      blocking_queue_model t γ []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    iMod (auth_excl_alloc' (auth_excl_G := blocking_queue_Gpre_model_G) []) as "(%γ & Hmodel₁ & Hmodel₂)".
    wp_apply (queue_make_spec with "[//]"). iIntros "%q Hmodel_q".
    wp_smart_apply (mutex_make_spec _ (blocking_queue_inv_inner γ q) with "[Hmodel_q Hmodel₂]").
    { iExists []. iFrame. }
    iIntros "%mtx #Hinv_mtx".
    wp_pures.
    iApply "HΦ". iFrame. iExists q, mtx. auto.
  Qed.

  Lemma blocking_queue_push_spec t γ v :
    <<<
      blocking_queue_inv t γ
    | ∀∀ vs, blocking_queue_model t γ vs
    >>>
      blocking_queue_push t v
    <<<
      blocking_queue_model t γ (v :: vs)
    | RET #(); True
    >>>.
  Proof.
    iIntros "!> %Φ (%q & %mtx & -> & #Hinv_mtx) HΦ".
    wp_rec.
    wp_smart_apply (mutex_protect_spec _ Φ with "[$Hinv_mtx HΦ]"); last auto. iIntros "Hlocked_mtx (%vs & Hmodel_q & Hmodel₂)".
    iApply wp_fupd.
    wp_smart_apply (queue_push_spec with "Hmodel_q"). iIntros "Hmodel_q".
    iMod "HΦ" as "(%_vs & Hmodel₁ & _ & HΦ)".
    iDestruct (auth_excl_agree_L with "Hmodel₁ Hmodel₂") as %->.
    set vs' := v :: vs.
    iMod (auth_excl_update' (auth_excl_G := blocking_queue_Gpre_model_G) vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "Hmodel₁") as "HΦ".
    iModIntro. iFrame. iSplitL "Hmodel_q Hmodel₂".
    { iExists vs'. iFrame. }
    iApply ("HΦ" with "[//]").
  Qed.

  Lemma blocking_queue_pop_spec t γ :
    <<<
      blocking_queue_inv t γ
    | ∀∀ vs, blocking_queue_model t γ vs
    >>>
      blocking_queue_pop t
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          blocking_queue_model t γ []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          blocking_queue_model t γ vs'
      end
    | RET o; True
    >>>.
  Proof.
    iIntros "!> %Φ (%q & %mtx & -> & #Hinv_mtx) HΦ".
    wp_rec.
    wp_smart_apply (mutex_protect_spec _ Φ with "[$Hinv_mtx HΦ]"); last auto. iIntros "Hlocked_mtx (%vs & Hmodel_q & Hmodel₂)".
    iApply wp_fupd.
    wp_smart_apply (queue_pop_spec with "Hmodel_q").
    iMod "HΦ" as "(%_vs & Hmodel₁ & _ & HΦ)".
    iDestruct (auth_excl_agree_L with "Hmodel₁ Hmodel₂") as %->.
    iIntros ([v |]).
    - iIntros "(%vs' & -> & Hmodel_q)".
      iMod (auth_excl_update' (auth_excl_G := blocking_queue_Gpre_model_G) vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" $! (Some v) with "[Hmodel₁]") as "HΦ".
      { iExists vs'. auto. }
      iModIntro. iFrame. iSplitL "Hmodel_q Hmodel₂".
      { iExists vs'. iFrame. }
      iApply ("HΦ" with "[//]").
    - iIntros "(-> & Hmodel_q)".
      iMod ("HΦ" $! None with "[$Hmodel₁ //]") as "HΦ".
      iModIntro. iFrame. iSplitL "Hmodel_q Hmodel₂".
      { iExists []. iFrame. }
      iApply ("HΦ" with "[//]").
  Qed.

  Program Definition blocking_mpmc_queue : mpmc_queue Σ false := {|
    mpmc_queue_make :=
      blocking_queue_make ;
    mpmc_queue_push :=
      blocking_queue_push ;
    mpmc_queue_pop :=
      blocking_queue_pop ;

    mpmc_queue_inv t γ _ :=
      blocking_queue_inv t γ ;
    mpmc_queue_model t γ vs :=
      blocking_queue_model t γ vs ;
  |}.
  Next Obligation.
    eauto using blocking_queue_make_spec.
  Qed.
  Next Obligation.
    setoid_rewrite <- (atomic_triple_mask_weaken ∅); last solve_ndisj.
    eauto using blocking_queue_push_spec.
  Qed.
  Next Obligation.
    setoid_rewrite <- (atomic_triple_mask_weaken ∅); last solve_ndisj.
    eauto using blocking_queue_pop_spec.
  Qed.
  Next Obligation.
    done.
  Qed.
End blocking_queue_G.

#[global] Opaque blocking_queue_make.
#[global] Opaque blocking_queue_push.
#[global] Opaque blocking_queue_pop.

#[global] Opaque blocking_queue_inv.
#[global] Opaque blocking_queue_model.
