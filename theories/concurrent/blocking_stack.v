From caml5 Require Import
  prelude.
From caml5.base_logic Require Import
  lib.auth_excl.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Import
  stack.
From caml5.concurrent Require Export
  base.
From caml5.concurrent Require Import
  mutex
  mpmc_stack.

Class BlockingStackGpre Σ `{!heapGS Σ} := {
  #[local] blocking_stack_Gpre_model_G :: AuthExclG Σ (leibnizO (list val)) ;
}.

Class BlockingStackG Σ `{!heapGS Σ} := {
  #[local] blocking_stack_G_Gpre :: BlockingStackGpre Σ ;
  blocking_stack_G_stack : stack Σ false ;
  blocking_stack_G_mutex : mutex Σ false ;
}.

Definition blocking_stack_Σ := #[
  auth_excl_Σ (leibnizO (list val))
].
#[global] Instance subG_blocking_stack_Σ Σ `{!heapGS Σ} :
  subG blocking_stack_Σ Σ →
  BlockingStackGpre Σ.
Proof.
  solve_inG.
Qed.

Section blocking_stack_G.
  Context `{blocking_stack_G : BlockingStackG Σ}.
  Implicit Types v t : val.
  Implicit Types vs : list val.

  Let stack := blocking_stack_G.(blocking_stack_G_stack).
  Let mutex := blocking_stack_G.(blocking_stack_G_mutex).

  Notation "t '.(stack)'" := t.1%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(mutex)'" := t.2%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(stack)'" := t.1%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(mutex)'" := t.2%E
  ( at level 5
  ) : expr_scope.

  Definition blocking_stack_make : val :=
    λ: <>,
      let: "stk" := stack.(stack_make) #() in
      let: "mtx" := mutex.(mutex_make) #() in
      ("stk", "mtx").

  Definition blocking_stack_push : val :=
    λ: "t" "v",
      mutex.(mutex_protect) "t".(mutex) (λ: <>,
        stack.(stack_push) "t".(stack) "v"
      ).

  Definition blocking_stack_pop : val :=
    λ: "t",
      mutex.(mutex_protect) "t".(mutex) (λ: <>,
        stack.(stack_pop) "t".(stack)
      ).

  #[local] Definition blocking_stack_inv_inner γ stk : iProp Σ :=
    ∃ vs,
    stack.(stack_model) stk vs ∗
    auth_excl_frag γ vs.
  Definition blocking_stack_inv t γ : iProp Σ :=
    ∃ stk mtx,
    ⌜t = (stk, mtx)%V⌝ ∗
    mutex.(mutex_inv) mtx (blocking_stack_inv_inner γ stk).

  Definition blocking_stack_model t γ vs :=
    auth_excl_auth γ (DfracOwn 1) vs.

  #[global] Instance blocking_stack_inv_persistent t γ :
    Persistent (blocking_stack_inv t γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance blocking_stack_model_timeless t γ vs :
    Timeless (blocking_stack_model t γ vs).
  Proof.
    apply _.
  Qed.

  Lemma blocking_stack_make_spec :
    {{{ True }}}
      blocking_stack_make #()
    {{{ t γ,
      RET t;
      blocking_stack_inv t γ ∗
      blocking_stack_model t γ []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    iMod (auth_excl_alloc' (auth_excl_G := blocking_stack_Gpre_model_G) []) as "(%γ & Hmodel₁ & Hmodel₂)".
    wp_apply (stack_make_spec with "[//]"). iIntros "%stk Hmodel_stk".
    wp_smart_apply (mutex_make_spec _ (blocking_stack_inv_inner γ stk) with "[Hmodel_stk Hmodel₂]").
    { iExists []. iFrame. }
    iIntros "%mtx #Hinv_mtx".
    wp_pures.
    iApply "HΦ". iFrame. iExists stk, mtx. auto.
  Qed.

  Lemma blocking_stack_push_spec t γ v :
    <<<
      blocking_stack_inv t γ
    | ∀∀ vs, blocking_stack_model t γ vs
    >>>
      blocking_stack_push t v
    <<<
      blocking_stack_model t γ (v :: vs)
    | RET #(); True
    >>>.
  Proof.
    iIntros "!> %Φ (%stk & %mtx & -> & #Hinv_mtx) HΦ".
    wp_rec.
    wp_smart_apply (mutex_protect_spec _ Φ with "[$Hinv_mtx HΦ]"); last auto. iIntros "Hlocked_mtx (%vs & Hmodel_stk & Hmodel₂)".
    iApply wp_fupd.
    wp_smart_apply (stack_push_spec with "Hmodel_stk"). iIntros "Hmodel_stk".
    iMod "HΦ" as "(%_vs & Hmodel₁ & _ & HΦ)".
    iDestruct (auth_excl_agree_L with "Hmodel₁ Hmodel₂") as %->.
    set vs' := v :: vs.
    iMod (auth_excl_update' (auth_excl_G := blocking_stack_Gpre_model_G) vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "Hmodel₁") as "HΦ".
    iModIntro. iFrame. iSplitL "Hmodel_stk Hmodel₂".
    { iExists vs'. iFrame. }
    iApply ("HΦ" with "[//]").
  Qed.

  Lemma blocking_stack_pop_spec t γ :
    <<<
      blocking_stack_inv t γ
    | ∀∀ vs, blocking_stack_model t γ vs
    >>>
      blocking_stack_pop t
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          blocking_stack_model t γ []
      | Some v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          blocking_stack_model t γ vs'
      end
    | RET o; True
    >>>.
  Proof.
    iIntros "!> %Φ (%stk & %mtx & -> & #Hinv_mtx) HΦ".
    wp_rec.
    wp_smart_apply (mutex_protect_spec _ Φ with "[$Hinv_mtx HΦ]"); last auto. iIntros "Hlocked_mtx (%vs & Hmodel_stk & Hmodel₂)".
    iApply wp_fupd.
    wp_smart_apply (stack_pop_spec with "Hmodel_stk").
    iMod "HΦ" as "(%_vs & Hmodel₁ & _ & HΦ)".
    iDestruct (auth_excl_agree_L with "Hmodel₁ Hmodel₂") as %->.
    iIntros ([v |]).
    - iIntros "(%vs' & -> & Hmodel_stk)".
      iMod (auth_excl_update' (auth_excl_G := blocking_stack_Gpre_model_G) vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" $! (Some v) with "[Hmodel₁]") as "HΦ".
      { iExists vs'. auto. }
      iModIntro. iFrame. iSplitL "Hmodel_stk Hmodel₂".
      { iExists vs'. iFrame. }
      iApply ("HΦ" with "[//]").
    - iIntros "(-> & Hmodel_stk)".
      iMod ("HΦ" $! None with "[$Hmodel₁ //]") as "HΦ".
      iModIntro. iFrame. iSplitL "Hmodel_stk Hmodel₂".
      { iExists []. iFrame. }
      iApply ("HΦ" with "[//]").
  Qed.

  Program Definition blocking_mpmc_stack : mpmc_stack Σ false := {|
    mpmc_stack_make :=
      blocking_stack_make ;
    mpmc_stack_push :=
      blocking_stack_push ;
    mpmc_stack_pop :=
      blocking_stack_pop ;

    mpmc_stack_inv t γ _ :=
      blocking_stack_inv t γ ;
    mpmc_stack_model t γ vs :=
      blocking_stack_model t γ vs ;
  |}.
  Next Obligation.
    eauto using blocking_stack_make_spec.
  Qed.
  Next Obligation.
    setoid_rewrite <- (atomic_triple_mask_weaken ∅); last solve_ndisj.
    eauto using blocking_stack_push_spec.
  Qed.
  Next Obligation.
    setoid_rewrite <- (atomic_triple_mask_weaken ∅); last solve_ndisj.
    eauto using blocking_stack_pop_spec.
  Qed.
  Next Obligation.
    done.
  Qed.
End blocking_stack_G.

#[global] Opaque blocking_stack_make.
#[global] Opaque blocking_stack_push.
#[global] Opaque blocking_stack_pop.

#[global] Opaque blocking_stack_inv.
#[global] Opaque blocking_stack_model.
