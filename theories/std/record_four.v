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

  Definition record_four_make : val :=
    λ: "v₀" "v₁" "v₂" "v₃",
      let: "l" := AllocN #4 "v₀" in
      "l".1 <- "v₁" ;;
      "l".2 <- "v₂" ;;
      "l".3 <- "v₃" ;;
      "l".

  Definition record_four_model l dq v₀ v₁ v₂ v₃ : iProp Σ :=
    (l +ₗ 0%Z) ↦{dq} v₀ ∗
    (l +ₗ 1%Z) ↦{dq} v₁ ∗
    (l +ₗ 2%Z) ↦{dq} v₂ ∗
    (l +ₗ 3%Z) ↦{dq} v₃.

  #[global] Instance record_four_model_timeless l dq v₀ v₁ v₂ v₃ :
    Timeless (record_four_model l dq v₀ v₁ v₂ v₃).
  Proof.
    apply _.
  Qed.
  #[global] Instance record_four_model_persistent l v₀ v₁ v₂ v₃ :
    Persistent (record_four_model l DfracDiscarded v₀ v₁ v₂ v₃).
  Proof.
    apply _.
  Qed.

  #[global] Instance record_four_model_fractional l v₀ v₁ v₂ v₃ :
    Fractional (λ q, record_four_model l (DfracOwn q) v₀ v₁ v₂ v₃).
  Proof.
    apply _.
  Qed.
  #[global] Instance record_four_model_as_fractional l q v₀ v₁ v₂ v₃ :
    AsFractional (record_four_model l (DfracOwn q) v₀ v₁ v₂ v₃) (λ q, record_four_model l (DfracOwn q) v₀ v₁ v₂ v₃) q.
  Proof.
    split; done || apply _.
  Qed.

  Lemma record_four_model_persist l dq v₀ v₁ v₂ v₃ :
    record_four_model l dq v₀ v₁ v₂ v₃ ==∗
    record_four_model l DfracDiscarded v₀ v₁ v₂ v₃.
  Proof.
    iIntros "(Hv₀ & Hv₁ & Hv₂ & Hv₃)".
    iMod (mapsto_persist with "Hv₀") as "$".
    iMod (mapsto_persist with "Hv₁") as "$".
    iMod (mapsto_persist with "Hv₂") as "$".
    iMod (mapsto_persist with "Hv₃") as "$".
    done.
  Qed.

  Lemma record_four_model_valid l dq v₀ v₁ v₂ v₃ :
    record_four_model l dq v₀ v₁ v₂ v₃ -∗
    ⌜✓ dq⌝.
  Proof.
    iIntros "(Hv₀ & Hv₁ & Hv₂ & Hv₃)". iApply (mapsto_valid with "Hv₀").
  Qed.
  Lemma record_four_model_combine l dq1 v₀1 v₁1 v₂1 v₃1 dq2 v₀2 v₁2 v₂2 v₃2 :
    record_four_model l dq1 v₀1 v₁1 v₂1 v₃1 -∗
    record_four_model l dq2 v₀2 v₁2 v₂2 v₃2 -∗
      record_four_model l (dq1 ⋅ dq2) v₀1 v₁1 v₂1 v₃1 ∗
      ⌜v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2 ∧ v₃1 = v₃2⌝.
  Proof.
    iIntros "(Hv₀1 & Hv₁1 & Hv₂1 & Hv₃1) (Hv₀2 & Hv₁2 & Hv₂2 & Hv₃2)".
    iDestruct (mapsto_combine with "Hv₀1 Hv₀2") as "(Hv₀ & <-)".
    iDestruct (mapsto_combine with "Hv₁1 Hv₁2") as "(Hv₁ & <-)".
    iDestruct (mapsto_combine with "Hv₂1 Hv₂2") as "(Hv₂ & <-)".
    iDestruct (mapsto_combine with "Hv₃1 Hv₃2") as "(Hv₃ & <-)".
    iSplit; last done. iFrame.
  Qed.
  Lemma record_four_model_valid_2 l dq1 v₀1 v₁1 v₂1 v₃1 dq2 v₀2 v₁2 v₂2 v₃2 :
    record_four_model l dq1 v₀1 v₁1 v₂1 v₃1 -∗
    record_four_model l dq2 v₀2 v₁2 v₂2 v₃2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2 ∧ v₃1 = v₃2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record_four_model_combine with "Hl1 Hl2") as "(Hl & %)".
    iDestruct (record_four_model_valid with "Hl") as %?.
    done.
  Qed.
  Lemma record_four_model_agree l dq1 v₀1 v₁1 v₂1 v₃1 dq2 v₀2 v₁2 v₂2 v₃2 :
    record_four_model l dq1 v₀1 v₁1 v₂1 v₃1 -∗
    record_four_model l dq2 v₀2 v₁2 v₂2 v₃2 -∗
    ⌜v₀1 = v₀2 ∧ v₁1 = v₁2 ∧ v₂1 = v₂2 ∧ v₃1 = v₃2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record_four_model_valid_2 with "Hl1 Hl2") as %?. naive_solver.
  Qed.
  Lemma record_four_model_dfrac_ne l1 dq1 v₀1 v₁1 v₂1 v₃1 l2 dq2 v₀2 v₁2 v₂2 v₃2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    record_four_model l1 dq1 v₀1 v₁1 v₂1 v₃1 -∗
    record_four_model l2 dq2 v₀2 v₁2 v₂2 v₃2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    iIntros "% Hl1 Hl2" (->).
    iDestruct (record_four_model_valid_2 with "Hl1 Hl2") as %?. naive_solver.
  Qed.
  Lemma record_four_model_ne l1 v₀1 v₁1 v₂1 v₃1 l2 dq2 v₀2 v₁2 v₂2 v₃2 :
    record_four_model l1 (DfracOwn 1) v₀1 v₁1 v₂1 v₃1 -∗
    record_four_model l2 dq2 v₀2 v₁2 v₂2 v₃2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    iApply record_four_model_dfrac_ne. intros []%exclusive_l. apply _.
  Qed.
  Lemma record_four_model_exclusive l v₀1 v₁1 v₂1 v₃1 v₀2 v₁2 v₂2 v₃2 :
    record_four_model l (DfracOwn 1) v₀1 v₁1 v₂1 v₃1 -∗
    record_four_model l (DfracOwn 1) v₀2 v₁2 v₂2 v₃2 -∗
    False.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (record_four_model_ne with "Hl1 Hl2") as %?. naive_solver.
  Qed.

  Lemma record_four_dfrac_relax dq l v₀ v₁ v₂ v₃ :
    ✓ dq →
    record_four_model l (DfracOwn 1) v₀ v₁ v₂ v₃ ==∗
    record_four_model l dq v₀ v₁ v₂ v₃.
  Proof.
    iIntros "% (Hv₀ & Hv₁ & Hv₂ & Hv₃)".
    iMod (mapsto_dfrac_relax with "Hv₀") as "Hv₀"; first done.
    iMod (mapsto_dfrac_relax with "Hv₁") as "Hv₁"; first done.
    iMod (mapsto_dfrac_relax with "Hv₂") as "Hv₂"; first done.
    iMod (mapsto_dfrac_relax with "Hv₃") as "Hv₃"; first done.
    iFrame. done.
  Qed.

  Lemma record_four_make_spec v₀ v₁ v₂ v₃ :
    {{{ True }}}
      record_four_make v₀ v₁ v₂ v₃
    {{{ l, RET #l; record_four_model l (DfracOwn 1) v₀ v₁ v₂ v₃ }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec. wp_pures. wp_alloc l as "Hl"; first done. wp_pures.
    iDestruct (array_cons with "Hl") as "(Hv₀ & Hl)".
    iEval (setoid_rewrite <- loc_add_0) in "Hv₀".
    iDestruct (array_cons with "Hl") as "(Hv₁ & Hl)".
    iDestruct (array_cons with "Hl") as "(Hv₂ & Hl)".
    rewrite loc_add_assoc Z.add_1_r -Z.two_succ.
    iDestruct (array_singleton with "Hl") as "Hv₃".
    rewrite loc_add_assoc Z.add_1_r. assert (Z.succ 2 = 3)%Z as -> by lia.
    wp_store. wp_store. wp_store.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.

  Lemma record_four_get0_spec l dq v₀ v₁ v₂ v₃ :
    {{{ record_four_model l dq v₀ v₁ v₂ v₃ }}}
      !#(l +ₗ 0)
    {{{ RET v₀; record_four_model l dq v₀ v₁ v₂ v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_load.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.
  Lemma record_four_get1_spec l dq v₀ v₁ v₂ v₃ :
    {{{ record_four_model l dq v₀ v₁ v₂ v₃ }}}
      !#(l +ₗ 1)
    {{{ RET v₁; record_four_model l dq v₀ v₁ v₂ v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_load.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.
  Lemma record_four_get2_spec l dq v₀ v₁ v₂ v₃ :
    {{{ record_four_model l dq v₀ v₁ v₂ v₃ }}}
      !#(l +ₗ 2)
    {{{ RET v₂; record_four_model l dq v₀ v₁ v₂ v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_load.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.
  Lemma record_four_get3_spec l dq v₀ v₁ v₂ v₃ :
    {{{ record_four_model l dq v₀ v₁ v₂ v₃ }}}
      !#(l +ₗ 3)
    {{{ RET v₃; record_four_model l dq v₀ v₁ v₂ v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_load.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.

  Lemma record_four_set0_spec l v₀ v₁ v₂ v₃ v :
    {{{ record_four_model l (DfracOwn 1) v₀ v₁ v₂ v₃ }}}
      #(l +ₗ 0) <- v
    {{{ RET #(); record_four_model l (DfracOwn 1) v v₁ v₂ v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_store.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.
  Lemma record_four_set1_spec l v₀ v₁ v₂ v₃ v :
    {{{ record_four_model l (DfracOwn 1) v₀ v₁ v₂ v₃ }}}
      #(l +ₗ 1) <- v
    {{{ RET #(); record_four_model l (DfracOwn 1) v₀ v v₂ v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_store.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.
  Lemma record_four_set2_spec l v₀ v₁ v₂ v₃ v :
    {{{ record_four_model l (DfracOwn 1) v₀ v₁ v₂ v₃ }}}
      #(l +ₗ 2) <- v
    {{{ RET #(); record_four_model l (DfracOwn 1) v₀ v₁ v v₃ }}}.
  Proof.
    iIntros "%Φ (Hv₀ & Hv₁ & Hv₂ & Hv₃) HΦ".
    wp_store.
    iApply ("HΦ" with "[$Hv₀ $Hv₁ $Hv₂ $Hv₃]").
  Qed.
End heapGS.

#[global] Opaque record_four_make.

#[global] Opaque record_four_model.
