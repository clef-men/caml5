From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.

Section heapGS.
  Context `{!heapGS Σ}.
  Implicit Types l : loc.

  Definition record2_make : val :=
    λ: "v₀" "v₁",
      let: "l" := AllocN #2 "v₀" in
      "l".1 <- "v₁" ;;
      "l".

  Definition record2_model l dq v₀ v₁ : iProp Σ :=
    (l +ₗ 0%Z) ↦{dq} v₀ ∗
    (l +ₗ 1%Z) ↦{dq} v₁.

  #[global] Instance record2_model_timeless l dq v₀ v₁ :
    Timeless (record2_model l dq v₀ v₁).
  Proof.
    apply _.
  Qed.
  #[global] Instance record2_model_persistent l v₀ v₁ :
    Persistent (record2_model l DfracDiscarded v₀ v₁).
  Proof.
    apply _.
  Qed.

  #[global] Instance record2_model_fractional l v₀ v₁ :
    Fractional (λ q, record2_model l (DfracOwn q) v₀ v₁).
  Proof.
    apply _.
  Qed.
  #[global] Instance record2_model_as_fractional l q v₀ v₁ :
    AsFractional (record2_model l (DfracOwn q) v₀ v₁) (λ q, record2_model l (DfracOwn q) v₀ v₁) q.
  Proof.
    split; done || apply _.
  Qed.

  Lemma record2_model_persist l dq v₀ v₁ :
    record2_model l dq v₀ v₁ ==∗
    record2_model l DfracDiscarded v₀ v₁.
  Proof.
    iIntros "(Hv₀ & Hv₁)".
    iMod (mapsto_persist with "Hv₀") as "$".
    iMod (mapsto_persist with "Hv₁") as "$".
    done.
  Qed.

  Lemma record2_model_valid l dq v₀ v₁ :
    record2_model l dq v₀ v₁ -∗
    ⌜✓ dq⌝.
  Proof.
    iIntros "(Hv₀ & Hv₁)". iApply (mapsto_valid with "Hv₀").
  Qed.
  Lemma record2_model_combine l dq1 v₀1 v₁1 dq2 v₀2 v₁2 :
    record2_model l dq1 v₀1 v₁1 -∗
    record2_model l dq2 v₀2 v₁2 -∗
      record2_model l (dq1 ⋅ dq2) v₀1 v₁1 ∗
      ⌜v₀1 = v₀2 ∧ v₁1 = v₁2⌝.
  Proof.
    iIntros "(Hv₀1 & Hv₁1) (Hv₀2 & Hv₁2)".
    iDestruct (mapsto_combine with "Hv₀1 Hv₀2") as "(Hv₀ & <-)".
    iDestruct (mapsto_combine with "Hv₁1 Hv₁2") as "(Hv₁ & <-)".
    iSplit; last done. iFrame.
  Qed.
  Lemma record2_model_valid_2 l dq1 v₀1 v₁1 dq2 v₀2 v₁2 :
    record2_model l dq1 v₀1 v₁1 -∗
    record2_model l dq2 v₀2 v₁2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ v₀1 = v₀2 ∧ v₁1 = v₁2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record2_model_combine with "Hl1 Hl2") as "(Hl & %)".
    iDestruct (record2_model_valid with "Hl") as %?.
    done.
  Qed.
  Lemma record2_model_agree l dq1 v₀1 v₁1 dq2 v₀2 v₁2 :
    record2_model l dq1 v₀1 v₁1 -∗
    record2_model l dq2 v₀2 v₁2 -∗
    ⌜v₀1 = v₀2 ∧ v₁1 = v₁2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record2_model_valid_2 with "Hl1 Hl2") as %?. naive_solver.
  Qed.
  Lemma record2_model_dfrac_ne l1 dq1 v₀1 v₁1 l2 dq2 v₀2 v₁2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    record2_model l1 dq1 v₀1 v₁1 -∗
    record2_model l2 dq2 v₀2 v₁2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    iIntros "% Hl1 Hl2" (->).
    iDestruct (record2_model_valid_2 with "Hl1 Hl2") as %?. naive_solver.
  Qed.
  Lemma record2_model_ne l1 v₀1 v₁1 l2 dq2 v₀2 v₁2 :
    record2_model l1 (DfracOwn 1) v₀1 v₁1 -∗
    record2_model l2 dq2 v₀2 v₁2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    iApply record2_model_dfrac_ne. intros []%exclusive_l. apply _.
  Qed.
  Lemma record2_model_exclusive l v₀1 v₁1 v₀2 v₁2 :
    record2_model l (DfracOwn 1) v₀1 v₁1 -∗
    record2_model l (DfracOwn 1) v₀2 v₁2 -∗
    False.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record2_model_ne with "Hl1 Hl2") as %?. naive_solver.
  Qed.

  Lemma record2_dfrac_relax dq l v₀ v₁ :
    ✓ dq →
    record2_model l (DfracOwn 1) v₀ v₁ ==∗
    record2_model l dq v₀ v₁.
  Proof.
    iIntros "% (Hv₀ & Hv₁)".
    iMod (mapsto_dfrac_relax with "Hv₀") as "Hv₀"; first done.
    iMod (mapsto_dfrac_relax with "Hv₁") as "Hv₁"; first done.
    iFrame. done.
  Qed.

  Lemma record2_make_spec v₀ v₁ :
    {{{ True }}}
      record2_make v₀ v₁
    {{{ l, RET #l; record2_model l (DfracOwn 1) v₀ v₁ }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec. wp_pures. wp_alloc l as "Hl"; first done. wp_pures.
    iDestruct (array_cons with "Hl") as "(Hv₀ & Hl)".
    iEval (setoid_rewrite <- loc_add_0) in "Hv₀".
    iDestruct (array_singleton with "Hl") as "Hv₁".
    wp_store.
    iApply ("HΦ" with "[$Hv₀ $Hv₁]").
  Qed.

  Lemma record2_get0_spec l dq v₀ v₁ :
    {{{ record2_model l dq v₀ v₁ }}}
      !#(l +ₗ 0)
    {{{ RET v₀; record2_model l dq v₀ v₁ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁) HΦ".
    wp_load.
    iApply ("HΦ" with "[$Hv₀ $Hv₁]").
  Qed.
  Lemma record2_get1_spec l dq v₀ v₁ :
    {{{ record2_model l dq v₀ v₁ }}}
      !#(l +ₗ 1)
    {{{ RET v₁; record2_model l dq v₀ v₁ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁) HΦ".
    wp_load.
    iApply ("HΦ" with "[$Hv₀ $Hv₁]").
  Qed.

  Lemma record2_set0_spec l v₀ v₁ v :
    {{{ record2_model l (DfracOwn 1) v₀ v₁ }}}
      #(l +ₗ 0) <- v
    {{{ RET #(); record2_model l (DfracOwn 1) v v₁ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁) HΦ".
    wp_store.
    iApply ("HΦ" with "[$Hv₀ $Hv₁]").
  Qed.
  Lemma record2_set1_spec l v₀ v₁ v :
    {{{ record2_model l (DfracOwn 1) v₀ v₁ }}}
      #(l +ₗ 1) <- v
    {{{ RET #(); record2_model l (DfracOwn 1) v₀ v }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁) HΦ".
    wp_store.
    iApply ("HΦ" with "[$Hv₀ $Hv₁]").
  Qed.
End heapGS.

#[global] Opaque record2_make.

#[global] Opaque record2_model.
