From iris.algebra Require Import
  list.

From caml5 Require Import
  prelude.
From caml5.base_logic Require Import
  lib.auth_excl.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Import
  mlst.
From caml5.concurrent Require Import
  mpmc_stack.
From caml5.concurrent Require Export
  base.

Definition treiber_stack_namespace :=
  concurrent_namespace .@ "treiber_stack".

Class TreiberG Σ `{!heapGS Σ} := {
  treiber_stack_G_model_G : AuthExclG Σ (listO valO) ;
}.
#[local] Existing Instance treiber_stack_G_model_G.

Definition treiber_stack_Σ := #[
  auth_excl_Σ (listO valO)
].
#[global] Instance subG_treiber_stack_Σ Σ `{!heapGS Σ} :
  subG treiber_stack_Σ Σ →
  TreiberG Σ.
Proof.
  solve_inG.
Qed.

Section treiber_stack_GS.
  Context `{TreiberG Σ}.
  Implicit Types l : loc.
  Implicit Types v t lst : val.

  Definition treiber_stack_make : val :=
    λ: <>,
      ref mlst_nil.

  Definition treiber_stack_push : val :=
    rec: "treiber_stack_push" "t" "v" :=
      let: "old_contents" := !"t" in
      if: CAS "t" "old_contents" (mlst_cons "v" "old_contents") then (
        #()
      ) else (
        "treiber_stack_push" "t" "v"
      ).

  Definition treiber_stack_pop : val :=
    rec: "treiber_stack_pop" "t" :=
      let: "old_contents" := !"t" in
      if: mlst_is_empty "old_contents" then (
        NONE
      ) else (
        let: "v" := mlst_head "old_contents" in
        let: "contents" := mlst_tail "old_contents" in
        if: CAS "t" "old_contents" "contents" then (
          SOME "v"
        ) else (
          "treiber_stack_pop" "t"
        )
      ).

  Notation treiber_stack_meta_model := (nroot .@ "model").

  #[local] Definition treiber_stack_model₁ γ vs : iProp Σ :=
    auth_excl_frag γ vs.
  #[local] Definition treiber_stack_model₂ γ vs : iProp Σ :=
    auth_excl_auth γ (DfracOwn 1) vs.

  Definition treiber_stack_inv_inner t l γ : iProp Σ :=
    ∃ lst vs,
    l ↦ lst ∗ mlst_model lst DfracDiscarded vs ∗ treiber_stack_model₁ γ vs.
  Definition treiber_stack_inv t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l treiber_stack_meta_model γ ∗
    inv treiber_stack_namespace (treiber_stack_inv_inner t l γ).

  Definition treiber_stack_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l treiber_stack_meta_model γ ∗
    treiber_stack_model₂ γ vs.

  #[global] Instance treiber_stack_inv_persistent t :
    Persistent (treiber_stack_inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance treiber_stack_model_timeless t vs :
    Timeless (treiber_stack_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma treiber_stack_make_spec :
    {{{ True }}}
      treiber_stack_make #()
    {{{ t, RET t; treiber_stack_inv t ∗ treiber_stack_model t [] }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    iApply wp_fupd. wp_apply (wp_alloc with "[//]"). iIntros "%l (Hl & Hmeta)".
    iApply "HΦ".
    iMod (auth_excl_alloc' []) as "(%γ & Hmodel₂ & Hmodel₁)".
    iMod (meta_set _ _ γ treiber_stack_meta_model with "Hmeta") as "#Hmeta"; first done.
    iSplitR "Hmodel₂"; iExists l, γ; iFrame "∗#"; last done.
    iSplitR; first done. iApply inv_alloc. iNext. iExists mlst_nil, []. iFrame "∗#".
    iApply mlst_nil_spec.
  Qed.

  Lemma treiber_stack_push_spec t v :
    <<< treiber_stack_inv t | ∀∀ vs, treiber_stack_model t vs >>>
      treiber_stack_push t v
      @ ↑ treiber_stack_namespace
    <<< treiber_stack_model t (v :: vs) | RET #(); True >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".
    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (! _)%E.
    iInv "Hinv" as "(%lst1 & %vs1 & Hl & #Hlst1 & Hmodel₁)".
    wp_load.
    iModIntro. iSplitL "Hl Hmodel₁".
    { iExists lst1, vs1. auto with iFrame. }

    wp_pures.
    wp_apply (mlst_cons_spec with "Hlst1"); first done. iIntros "%lst1' #Hlst1'".

    wp_bind (CmpXchg _ _ _).
    iInv "Hinv" as "(%lst2 & %vs2 & Hl & >#Hlst2 & Hmodel₁)".
    iDestruct (mlst_model_unboxed with "Hlst1") as %?. wp_cmpxchg as -> | ?.

    - iDestruct (mlst_model_agree with "Hlst1 Hlst2") as %<-.
      iMod "HΦ" as "(%_vs1 & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₂) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_both_agree_L with "Hmodel₂ Hmodel₁") as %->.
      iMod (auth_excl_update' (v :: vs1) with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
      iMod ("HΦ" with "[Hmodel₂] [//]") as "HΦ".
      { iExists l, γ. auto with iFrame. }
      iModIntro. iSplitL "Hl Hmodel₁".
      { iExists lst1', (v :: vs1). auto with iFrame. }

      wp_pures.

      iApply "HΦ".

    - iModIntro. iSplitL "Hl Hmodel₁".
      { iExists lst2, vs2. auto with iFrame. }

      wp_pures.

      wp_apply ("HLöb" with "HΦ").
  Qed.

  Lemma treiber_stack_pop_spec t :
    <<< treiber_stack_inv t | ∀∀ vs, treiber_stack_model t vs >>>
      treiber_stack_pop t
      @ ↑ treiber_stack_namespace
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ treiber_stack_model t []) ∨
      (∃ v vs', ⌜vs = v :: vs' ∧ o = SOMEV v⌝ ∗ treiber_stack_model t vs') |
      RET o; True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".
    iLöb as "HLöb".

    wp_rec.

    wp_bind (! _)%E.
    iInv "Hinv" as "(%lst1 & %vs1 & Hl & #Hlst1 & Hmodel₁)".
    wp_load.
    destruct vs1 as [| v1 vs1].

    - iMod "HΦ" as "(%_vs1 & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₂) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_both_agree_L with "Hmodel₂ Hmodel₁") as %->.
      iMod ("HΦ" with "[Hmodel₂] [//]") as "HΦ".
      { iLeft. iSplit; first done. iExists l, γ. auto with iFrame. }
      iModIntro. iSplitL "Hl Hmodel₁".
      { iExists lst1, []. auto with iFrame. }

      wp_pures.

      wp_apply (mlst_is_empty_spec with "Hlst1"). iIntros "_".

      wp_pures.

      iApply "HΦ".

    - iModIntro. iSplitL "Hl Hmodel₁".
      { iExists lst1, (v1 :: vs1). auto with iFrame. }

      wp_pures.

      wp_apply (mlst_is_empty_spec with "Hlst1"). iIntros "_".

      wp_pures.

      wp_apply (mlst_head_spec with "Hlst1"). iIntros "_".

      wp_pures.

      wp_apply (mlst_tail_spec with "Hlst1"). iIntros "%lst1' (_ & #Hlst1')".

      wp_pures.

      wp_bind (CmpXchg _ _ _).
      iInv "Hinv" as "(%lst2 & %vs2 & Hl & >#Hlst2 & Hmodel₁)".
      iDestruct (mlst_model_unboxed with "Hlst1") as %?. wp_cmpxchg as -> | ?.

      + iDestruct (mlst_model_agree with "Hlst1 Hlst2") as %<-.
        iMod "HΦ" as "(%_vs1 & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₂) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (auth_excl_both_agree_L with "Hmodel₂ Hmodel₁") as %->.
        iMod (auth_excl_update' vs1 with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
        iMod ("HΦ" with "[Hmodel₂] [//]") as "HΦ".
        { iRight. iExists v1, vs1. iSplit; first done. iExists l, γ. auto with iFrame. }
        iModIntro. iSplitL "Hl Hmodel₁".
        { iExists lst1', vs1. auto with iFrame. }

        wp_pures.

        iApply "HΦ".

      + iModIntro. iSplitL "Hl Hmodel₁".
        { iExists lst2, vs2. auto with iFrame. }

        wp_pures.

        wp_apply ("HLöb" with "HΦ").
  Qed.

  Definition treiber_mpmc_stack :=
    Build_mpmc_stack
      treiber_stack_make_spec
      treiber_stack_push_spec
      treiber_stack_pop_spec.
End treiber_stack_GS.

#[global] Opaque treiber_stack_make.
#[global] Opaque treiber_stack_push.
#[global] Opaque treiber_stack_pop.

#[global] Opaque treiber_stack_inv.
#[global] Opaque treiber_stack_model.
