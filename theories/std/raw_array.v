From caml5 Require Import
  prelude
  tactics.
From caml5.base_logic Require Import
  lib.auth_nat_max.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.

Class RawArrayG Σ `{!heapGS Σ} := {
  raw_array_G_token_G : AuthNatMaxG Σ ;
}.
#[local] Existing Instance raw_array_G_token_G.

Definition raw_array_Σ := #[
  auth_nat_max_Σ
].
#[global] Instance subG_raw_array_Σ Σ `{!heapGS Σ} :
  subG raw_array_Σ Σ →
  RawArrayG Σ.
Proof.
  solve_inG.
Qed.

Section raw_array_G.
  Context `{raw_array_G : RawArrayG Σ}.
  Implicit Types sz i j : nat.
  Implicit Types l : loc.
  Implicit Types v t : val.

  Definition raw_array_make : val :=
    λ: "sz" "v",
      AllocN "sz" "v".

  Definition raw_array_get : val :=
    λ: "t" "i",
      ! ("t" +ₗ "i").
  Definition raw_array_set : val :=
    λ: "t" "i" "v",
      "t" +ₗ "i" <- "v".

  Notation raw_array_meta_token := (nroot .@ "token").

  Section raw_array_token.
    #[local] Definition raw_array_token_auth γ sz :=
      auth_nat_max_auth γ DfracDiscarded sz.
    #[local] Definition raw_array_token_frag γ i :=
      auth_nat_max_frag γ i.

    #[local] Lemma raw_array_token_alloc sz :
      ⊢ |==> ∃ γ,
        raw_array_token_auth γ sz.
    Proof.
      iMod auth_nat_max_alloc as "(%γ & H●)".
      iMod (auth_nat_max_auth_persist with "H●") as "H●".
      iExists γ. done.
    Qed.
    #[local] Lemma raw_array_token_valid γ sz i :
      raw_array_token_auth γ sz -∗
      raw_array_token_frag γ i -∗
      ⌜i ≤ sz⌝.
    Proof.
      iApply auth_nat_max_valid.
    Qed.
    #[local] Lemma raw_array_token_frag_le γ i i' :
      i' ≤ i →
      raw_array_token_frag γ i -∗
      raw_array_token_frag γ i'.
    Proof.
      intros. iApply auth_nat_max_frag_le. done.
    Qed.
  End raw_array_token.

  Section raw_array_inv.
    Definition raw_array_inv t sz : iProp Σ :=
      ∃ l γ,
      ⌜t = #l⌝ ∗
      meta l raw_array_meta_token γ ∗
      ⌜0 < sz⌝ ∗ raw_array_token_auth γ sz.

    #[global] Instance raw_array_inv_persistent t sz :
      Persistent (raw_array_inv t sz).
    Proof.
      apply _.
    Qed.

    Lemma raw_array_inv_valid t sz :
      raw_array_inv t sz -∗
      ⌜0 < sz⌝.
    Proof.
      iIntros "(%l & %γ & -> & #Hmeta & $ & #H●)".
    Qed.
  End raw_array_inv.

  Section raw_array_mapsto.
    Definition raw_array_mapsto t i dq v : iProp Σ :=
      ∃ l γ,
      ⌜t = #l⌝ ∗
      meta l raw_array_meta_token γ ∗
      raw_array_token_frag γ (S i) ∗
      (l +ₗ i) ↦{dq} v.

    #[global] Instance raw_array_mapsto_timeless t i dq v :
      Timeless (raw_array_mapsto t i dq v).
    Proof.
      apply _.
    Qed.
    #[global] Instance raw_array_mapsto_persistent t i v :
      Timeless (raw_array_mapsto t i DfracDiscarded v).
    Proof.
      apply _.
    Qed.

    #[global] Instance raw_array_mapsto_fractional t i v :
      Fractional (λ q, raw_array_mapsto t i (DfracOwn q) v).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%l & %γ & -> & #Hmeta & #H◯ & H↦1 & H↦2)".
        iSplitL "H↦1"; repeat iExists _; naive_solver.
      - iIntros "((%l1 & %γ1 & % & #Hmeta1 & #H◯ & H↦1) & (%l2 & %γ2 & % & #Hmeta2 & _ & H↦2))". simplify.
        iDestruct (meta_agree with "Hmeta1 Hmeta2") as %->.
        repeat iExists _. iFrame. naive_solver.
    Qed.
    #[global] Instance raw_array_mapsto_as_fractional t i q v :
      AsFractional (raw_array_mapsto t i (DfracOwn q) v) (λ q, raw_array_mapsto t i (DfracOwn q) v) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma raw_array_mapsto_persist t i dq v :
      raw_array_mapsto t i dq v ==∗
      raw_array_mapsto t i DfracDiscarded v.
    Proof.
      iIntros "(%l & %γ & -> & Hmeta & #H◯ & H↦)".
      iMod (mapsto_persist with "H↦").
      repeat iExists _. naive_solver.
    Qed.

    Lemma raw_array_mapsto_valid t sz i dq v :
      raw_array_inv t sz -∗
      raw_array_mapsto t i dq v -∗
      ⌜✓ dq ∧ i < sz⌝.
    Proof.
      iIntros "(%l & %γ & % & #Hmeta & % & #H●) (%_l & %_γ & -> & #_Hmeta & #H◯ & H↦)". simplify.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mapsto_valid with "H↦") as %?.
      iDestruct (raw_array_token_valid with "H● H◯") as %?. done.
    Qed.
    Lemma raw_array_mapsto_valid_2 t i dq1 v1 dq2 v2 :
      raw_array_mapsto t i dq1 v1 -∗
      raw_array_mapsto t i dq2 v2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
    Proof.
      iIntros "(%l1 & %γ1 & % & #Hmeta1 & #H◯1 & H↦1) (%l2 & %γ2 & % & #Hmeta2 & #H◯2 & H↦2)". simplify.
      iDestruct (mapsto_valid_2 with "H↦1 H↦2") as %?. done.
    Qed.

    Lemma raw_array_mapsto_exclusive t i v1 v2 :
      raw_array_mapsto t i (DfracOwn 1) v1 -∗
      raw_array_mapsto t i (DfracOwn 1) v2 -∗
      False.
    Proof.
      iIntros "Hmapsto1 Hmapsto2".
      iDestruct (raw_array_mapsto_valid_2 with "Hmapsto1 Hmapsto2") as %(?%dfrac_valid_own_r & _). done.
    Qed.

    Lemma raw_array_mapsto_combine t i dq1 v1 dq2 v2 :
      raw_array_mapsto t i dq1 v1 -∗
      raw_array_mapsto t i dq2 v2 -∗
      raw_array_mapsto t i (dq1 ⋅ dq2) v1.
    Proof.
      iIntros "Hmapsto1 Hmapsto2".
      iDestruct (raw_array_mapsto_valid_2 with "Hmapsto1 Hmapsto2") as %(_ & ->).
      iDestruct "Hmapsto1" as "(%l & %γ & % & #Hmeta1 & #H◯1 & H↦1)".
      iDestruct "Hmapsto2" as "(%_l & %_γ & -> & #_Hmeta & #H◯2 & H↦2)". simplify.
      iDestruct (mapsto_combine with "H↦1 H↦2") as "(H↦ & _)".
      repeat iExists _. naive_solver.
    Qed.
  End raw_array_mapsto.

  Section raw_array_view.
    Definition raw_array_view t i dq vs : iProp Σ :=
      ∃ l γ,
      ⌜t = #l⌝ ∗
      meta l raw_array_meta_token γ ∗
      raw_array_token_frag γ (i + length vs) ∗
      [∗ list] j ↦ v ∈ vs, (l +ₗ (i + j)%nat) ↦{dq} v.

    #[global] Instance raw_array_view_timeless t i dq vs :
      Timeless (raw_array_view t i dq vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance raw_array_view_persistent t i vs :
      Timeless (raw_array_view t i DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance raw_array_view_fractional t i vs :
      Fractional (λ q, raw_array_view t i (DfracOwn q) vs).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%l & %γ & % & #Hmeta & #H◯ & Hvs)". simplify.
        iDestruct (fractional_big_sepL vs (λ j v q, (l +ₗ (i + j)%nat) ↦{#q} v)%I with "Hvs") as "(Hvs1 & Hvs2)".
        iSplitL "Hvs1"; repeat iExists _; naive_solver.
      - iIntros "((%l1 & %γ1 & % & #Hmeta1 & #H◯1 & Hvs1) & (%l2 & %γ2 & % & #Hmeta2 & #H◯2 & Hvs2))". simplify.
        iDestruct (meta_agree with "Hmeta1 Hmeta2") as %->.
        iDestruct (fractional_big_sepL vs (λ j v q, (l2 +ₗ (i + j)%nat) ↦{#q} v)%I with "[$Hvs1 $Hvs2]") as "Hvs".
        repeat iExists _; naive_solver.
    Qed.
    #[global] Instance raw_array_view_as_fractional t i q vs :
      AsFractional (raw_array_view t i (DfracOwn q) vs) (λ q, raw_array_view t i (DfracOwn q) vs) q.
    Proof.
      split; [done | apply _].
    Qed.

    #[local] Lemma raw_array_view_to_mapstos_strong t i dq vs :
      raw_array_view t i dq vs -∗
        ∃ l γ,
        ⌜t = #l⌝ ∗ meta l raw_array_meta_token γ ∗
        raw_array_token_frag γ (i + length vs) ∗
        [∗ list] j ↦ v ∈ vs, raw_array_mapsto t (i + j) dq v.
    Proof.
      iIntros "(%l & %γ & -> & #Hmeta & #H◯ & H↦s)".
      iExists l, γ. iFrame "∗#". iSplit; first done.
      iApply (big_sepL_impl with "H↦s"). iIntros "!> %j %v %Hlookup H↦".
      iExists l, γ. repeat iSplit; try done.
      iApply (raw_array_token_frag_le with "H◯").
      apply lookup_lt_Some in Hlookup. lia.
    Qed.
    Lemma raw_array_view_to_mapstos t i dq vs :
      raw_array_view t i dq vs -∗
      [∗ list] j ↦ v ∈ vs, raw_array_mapsto t (i + j) dq v.
    Proof.
      iIntros "Hview".
      iDestruct (raw_array_view_to_mapstos_strong with "Hview") as "(%l & %γ & _ & _ & _ & $)".
    Qed.

    #[local] Lemma raw_array_view_to_mapsto_strong {t i dq vs} j v :
      vs !! j = Some v →
      raw_array_view t i dq vs -∗
        ∃ l γ,
        ⌜t = #l⌝ ∗ meta l raw_array_meta_token γ ∗
        raw_array_token_frag γ (i + length vs) ∗
        raw_array_mapsto t (i + j) dq v.
    Proof.
      iIntros "% Hview".
      iDestruct (raw_array_view_to_mapstos_strong with "Hview") as "(%l & %γ & -> & #Hmeta & H◯ & Hmapstos)".
      iExists l, γ. iFrame "∗#". iSplit; first done.
      iApply (big_sepL_lookup with "Hmapstos"). done.
    Qed.
    Lemma raw_array_view_to_mapsto {t i dq vs} j v :
      vs !! j = Some v →
      raw_array_view t i dq vs -∗
      raw_array_mapsto t (i + j) dq v.
    Proof.
      iIntros "% Hview".
      iDestruct (raw_array_view_to_mapsto_strong with "Hview") as "(%l & %γ & _ & _ & _ &$)". done.
    Qed.

    #[local] Lemma raw_array_mapstos_to_view_strong t l γ i dq vs :
      t = #l →
      meta l raw_array_meta_token γ -∗
      raw_array_token_frag γ (i + length vs) -∗
      ([∗ list] j ↦ v ∈ vs, raw_array_mapsto t (i + j) dq v) -∗
      raw_array_view t i dq vs.
    Proof.
      iIntros "% #Hmeta #H◯ Hmapstos". simplify.
      iExists l, γ. repeat iSplit; try done.
      iApply (big_sepL_impl with "Hmapstos").
      iIntros "!> %j %v %Hlookup (%l' & %γ' & % & #Hmeta' & #H◯' & H↦)". simplify.
      done.
    Qed.
    Lemma raw_array_mapstos_to_view t i dq vs :
      0 < length vs →
      ([∗ list] j ↦ v ∈ vs, raw_array_mapsto t (i + j) dq v) -∗
      raw_array_view t i dq vs.
    Proof.
      iIntros "%Hvs Hmapstos".
      iDestruct (big_sepL_lookup_acc with "Hmapstos") as "((%l & %γ & -> & #Hmeta & #H◯ & H↦) & Hmapstos)".
      { destruct (nth_lookup_or_length vs (length vs - 1) #()); naive_solver lia. }
      assert (S (i + (length vs - 1)) = i + length vs) as Heq; first lia.
      iEval (rewrite Heq) in "H◯".
      iDestruct ("Hmapstos" with "[H↦]") as "Hmapstos".
      { iExists l, γ. iEval (rewrite Heq). naive_solver. }
      iApply (raw_array_mapstos_to_view_strong with "Hmeta H◯ Hmapstos"); first done.
    Qed.

    #[local] Lemma raw_array_view_map t i {dq1 vs1} dq2 vs2 :
      length vs2 = length vs1 →
      □ (∀ j,
        ⌜j < length vs1⌝ -∗
        raw_array_mapsto t (i + j) dq1 (vs1 !!! j) ==∗
        raw_array_mapsto t (i + j) dq2 (vs2 !!! j)
      ) -∗
      raw_array_view t i dq1 vs1 ==∗
      raw_array_view t i dq2 vs2.
    Proof.
      iIntros "%Hvs2 #H Hview".
      iDestruct (raw_array_view_to_mapstos_strong with "Hview") as "(%l & %γ & % & #Hmeta & #H◯ & Hmapstos)". simplify.
      rewrite -Hvs2. iApply (raw_array_mapstos_to_view_strong with "Hmeta H◯ [> Hmapstos]"); first done.
      iClear "Hmeta H◯". iApply big_sepL_bupd.
      remember (length vs1) as n eqn:Hvs1.
      iRevert "H Hmapstos". iInduction n as [| n] "IH" forall (i vs1 Hvs1 vs2 Hvs2); iIntros "#H Hmapstos".
      - rewrite (nil_length_inv vs2); done.
      - destruct vs1 as [| v1 vs1], vs2 as [| v2 vs2]; [done.. |].
        iDestruct "Hmapstos" as "(Hmapsto & Hmapstos)".
        iSplitL "Hmapsto".
        + iMod ("H" with "[] Hmapsto"); auto with lia.
        + setoid_rewrite Nat.add_succ_r.
          iApply ("IH" $! (S i) with "[] [] [] Hmapstos"); [auto with lia.. |].
          iIntros "!> %j %Hj Hmapsto /=".
          iSpecialize ("H" $! (S j) with "[] [Hmapsto]"); first auto with lia;
            rewrite Nat.add_succ_r //.
    Qed.

    Lemma raw_array_view_persist t i dq vs :
      raw_array_view t i dq vs ==∗
      raw_array_view t i DfracDiscarded vs.
    Proof.
      iIntros "Hview".
      iApply (raw_array_view_map with "[] Hview"); first done.
      iIntros "!> %j _ Hmapsto". iApply (raw_array_mapsto_persist with "Hmapsto").
    Qed.

    Lemma raw_array_view_valid t sz i dq vs :
      0 < length vs →
      raw_array_inv t sz -∗
      raw_array_view t i dq vs -∗
      ⌜✓ dq ∧ i + length vs ≤ sz⌝.
    Proof.
      iIntros "% #Hinv Hview".
      iDestruct (raw_array_view_to_mapsto (length vs - 1) with "Hview") as "Hmapsto".
      { destruct (nth_lookup_or_length vs (length vs - 1) inhabitant); naive_solver lia. }
      iDestruct (raw_array_mapsto_valid with "Hinv Hmapsto") as %?.
      iPureIntro. naive_solver lia.
    Qed.
    Lemma raw_array_view_valid_2 t i dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      raw_array_view t i dq1 vs1 -∗
      raw_array_view t i dq2 vs2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% % Hview1 Hview2".
      iDestruct (raw_array_view_to_mapstos with "Hview1") as "Hmapstos1".
      iDestruct (raw_array_view_to_mapstos with "Hview2") as "Hmapstos2".
      iAssert ⌜∀ j v1 v2, vs1 !! j = Some v1 → vs2 !! j = Some v2 → ✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝%I as %?; last first.
      { iPureIntro. split.
        - destruct (nth_lookup_or_length vs1 0 inhabitant) as []; last lia.
          destruct (nth_lookup_or_length vs2 0 inhabitant) as []; last lia.
          naive_solver.
        - eapply list_eq_same_length; naive_solver.
      }
      iDestruct (big_sepL2_sepL_2 with "Hmapstos1 Hmapstos2") as "Hmapstos"; first done.
      iApply big_sepL2_pure_1.
      iApply (big_sepL2_impl with "Hmapstos").
      iIntros "!> %j %v1 %v2 % % (Hmapsto1 & Hmapsto2)".
      iApply (raw_array_mapsto_valid_2 with "Hmapsto1 Hmapsto2").
    Qed.
    Lemma raw_array_view_agree t i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      raw_array_view t i dq1 vs1 -∗
      raw_array_view t i dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hview1 Hview2".
      destruct vs1 as [| v1 vs1], vs2 as [| v2 vs2]; try done.
      iDestruct (raw_array_view_valid_2 with "Hview1 Hview2") as %(_ & ->); try done.
      list_simplifier. lia.
    Qed.

    Lemma raw_array_view_exclusive t i vs1 vs2 :
      0 < length vs1 ≤ length vs2 →
      raw_array_view t i (DfracOwn 1) vs1 -∗
      raw_array_view t i (DfracOwn 1) vs2 -∗
      False.
    Proof.
      iIntros "% Hview1 Hview2".
      destruct vs1 as [| v1 vs1], vs2 as [| v2 vs2]; try naive_solver lia.
      iDestruct (raw_array_view_to_mapstos with "Hview1") as "(Hmapsto1 & _)".
      iDestruct (raw_array_view_to_mapstos with "Hview2") as "(Hmapsto2 & _)".
      iApply (raw_array_mapsto_exclusive with "Hmapsto1 Hmapsto2").
    Qed.

    Lemma raw_array_view_combine t i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      raw_array_view t i dq1 vs1 -∗
      raw_array_view t i dq2 vs2 -∗
      raw_array_view t i (dq1 ⋅ dq2) vs1.
    Proof.
      iIntros "% Hview1 Hview2".
      destruct (decide (0 < length vs1)) as [Hvs1 |]; last first.
      { rewrite (nil_length_inv vs1); last lia.
        rewrite (nil_length_inv vs2); last lia.
        auto.
      }
      iDestruct (raw_array_view_valid_2 with "Hview1 Hview2") as %(_ & <-); [done.. |].
      iDestruct "Hview1" as "(%l & %γ & % & #Hmeta & #H◯1 & H↦1)".
      iDestruct "Hview2" as "(%_l & %_γ & -> & _ & _ & H↦2)". simplify.
      iExists l, γ. iFrame "#". iSplit; first done.
      iDestruct (big_sepL_sep_2 with "H↦1 H↦2") as "H↦".
      iApply (big_sepL_impl with "H↦").
      iIntros "!> %j %v % (H↦1 & H↦2)".
      iDestruct (mapsto_combine with "H↦1 H↦2") as "($ & _)".
    Qed.

    Lemma raw_array_view_app t i dq n1 vs1 vs2 :
      n1 = length vs1 →
      raw_array_view t i dq vs1 -∗
      raw_array_view t (i + n1) dq vs2 -∗
      raw_array_view t i dq (vs1 ++ vs2).
    Proof.
      iIntros "% (%l & %γ & % & #Hmeta & _ & H↦1) (%_l & %_γ & -> & #_Hmeta & #H◯ & H↦2)". simplify.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (big_sepL_app _ vs1 vs2 with "[$H↦1 H↦2]") as "H↦".
      { iEval (setoid_rewrite (assoc Nat.add)). done. }
      iExists l, γ. iFrame "∗#". iSplit; first done.
      rewrite app_length assoc //.
    Qed.

    Lemma raw_array_view_split t i dq vs1 vs2 vs :
      vs = vs1 ++ vs2 →
      raw_array_view t i dq vs -∗
        raw_array_view t i dq vs1 ∗
        raw_array_view t (i + length vs1) dq vs2.
    Proof.
      iIntros (->) "(%l & %γ & -> & #Hmeta & #H◯ & H↦)".
      iDestruct (bi.equiv_entails_1_1 _ _ (big_sepL_app _ vs1 vs2) with "H↦") as "(H↦1 & H↦2)".
      iSplitL "H↦1"; iExists l, γ; iFrame "∗#"; (iSplit; first done).
      - iApply (raw_array_token_frag_le with "H◯"). rewrite app_length. lia.
      - rewrite app_length assoc. setoid_rewrite (assoc Nat.add). auto.
    Qed.
  End raw_array_view.

  Section raw_array_model.
    Definition raw_array_model t dq vs :=
      raw_array_view t 0 dq vs.

    #[global] Instance raw_array_model_timeless t dq vs :
      Timeless (raw_array_model t dq vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance raw_array_model_persistent t vs :
      Persistent (raw_array_model t DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance raw_array_model_fractional t vs :
      Fractional (λ q, raw_array_model t (DfracOwn q) vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance raw_array_model_as_fractional t q vs :
      AsFractional (raw_array_model t (DfracOwn q) vs) (λ q, raw_array_model t (DfracOwn q) vs) q.
    Proof.
      apply _.
    Qed.

    Lemma raw_array_model_persist t dq vs :
      raw_array_model t dq vs ==∗
      raw_array_model t DfracDiscarded vs.
    Proof.
      iApply raw_array_view_persist.
    Qed.

    Lemma raw_array_model_valid t sz dq vs :
      0 < length vs →
      raw_array_inv t sz -∗
      raw_array_model t dq vs -∗
      ⌜✓ dq ∧ length vs ≤ sz⌝.
    Proof.
      intros. iApply raw_array_view_valid. done.
    Qed.
    Lemma raw_array_model_valid_2 t dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      raw_array_model t dq1 vs1 -∗
      raw_array_model t dq2 vs2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      intros. iApply raw_array_view_valid_2; done.
    Qed.
    Lemma raw_array_model_agree t dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      raw_array_model t dq1 vs1 -∗
      raw_array_model t dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      intros. iApply raw_array_view_agree; done.
    Qed.

    Lemma raw_array_model_exclusive t vs1 vs2 :
      0 < length vs1 ≤ length vs2 →
      raw_array_model t (DfracOwn 1) vs1 -∗
      raw_array_model t (DfracOwn 1) vs2 -∗
      False.
    Proof.
      intros. iApply raw_array_view_exclusive; done.
    Qed.

    Lemma raw_array_model_combine t dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      raw_array_model t dq1 vs1 -∗
      raw_array_model t dq2 vs2 -∗
      raw_array_model t (dq1 ⋅ dq2) vs1.
    Proof.
      intros. iApply raw_array_view_combine. done.
    Qed.

    Lemma raw_array_model_split t dq vs1 vs2 vs :
      vs = vs1 ++ vs2 →
      raw_array_model t dq vs -∗
        raw_array_model t dq vs1 ∗
        raw_array_view t (length vs1) dq vs2.
    Proof.
      intros. iApply raw_array_view_split. done.
    Qed.
  End raw_array_model.

  Section raw_array_span.
    Definition raw_array_span t i dq n : iProp Σ :=
      ∃ vs,
      ⌜length vs = n⌝ ∗ raw_array_view t i dq vs.

    #[global] Instance raw_array_span_timeless t i dq n :
      Timeless (raw_array_span t i dq n).
    Proof.
      apply _.
    Qed.
    #[global] Instance raw_array_span_persistent t i n :
      Persistent (raw_array_span t i DfracDiscarded n).
    Proof.
      apply _.
    Qed.

    #[global] Instance raw_array_span_fractional t i n :
      Fractional (λ q, raw_array_span t i (DfracOwn q) n).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%vs & % & (Hview1 & Hview2))".
        iSplitL "Hview1"; iExists vs; auto.
      - iIntros "((%vs & % & Hview1) & (%_vs & % & Hview2))".
        iDestruct (raw_array_view_agree with "Hview1 Hview2") as %<-; [naive_solver.. |].
        iCombine "Hview1 Hview2" as "Hview".
        iExists vs. naive_solver.
    Qed.
    #[global] Instance raw_array_span_as_fractional t i q vs :
      AsFractional (raw_array_view t i (DfracOwn q) vs) (λ q, raw_array_view t i (DfracOwn q) vs) q.
    Proof.
      apply _.
    Qed.

    Lemma raw_array_span_view_1 t i dq n :
      raw_array_span t i dq n -∗
      ∃ vs, ⌜length vs = n⌝ ∗ raw_array_view t i dq vs.
    Proof.
      done.
    Qed.
    Lemma raw_array_span_view_2 t i dq vs :
      raw_array_view t i dq vs -∗
      raw_array_span t i dq (length vs).
    Proof.
      iIntros "Hview". iExists vs. naive_solver.
    Qed.
    Lemma raw_array_span_view t i dq n :
      raw_array_span t i dq n ⊣⊢
      ∃ vs, ⌜length vs = n⌝ ∗ raw_array_view t i dq vs.
    Proof.
      iSplit.
      - iApply raw_array_span_view_1.
      - iIntros "(%vs & % & Hview)". simplify.
        iApply (raw_array_span_view_2 with "Hview").
    Qed.

    Lemma raw_array_span_persist t i dq n :
      raw_array_span t i dq n ==∗
      raw_array_span t i DfracDiscarded n.
    Proof.
      iIntros "(%vs & % & Hview)".
      iExists vs. iSplitR; first done. iApply raw_array_view_persist. done.
    Qed.

    Lemma raw_array_span_valid t sz i dq n :
      0 < n →
      raw_array_inv t sz -∗
      raw_array_span t i dq n -∗
      ⌜✓ dq ∧ i + n ≤ sz⌝.
    Proof.
      iIntros "% #Hinv (%vs & % & Hview)".
      iDestruct (raw_array_view_valid with "Hinv Hview") as %?; naive_solver.
    Qed.

    Lemma raw_array_span_exclusive t i n1 n2 :
      0 < n1 ≤ n2 →
      raw_array_span t i (DfracOwn 1) n1 -∗
      raw_array_span t i (DfracOwn 1) n2 -∗
      False.
    Proof.
      iIntros "% (%vs1 & % & Hview1) (%vs2 & % & Hview2)".
      iApply (raw_array_view_exclusive with "Hview1 Hview2"). lia.
    Qed.

    Lemma raw_array_span_combine t i dq1 dq2 n :
      raw_array_span t i dq1 n -∗
      raw_array_span t i dq2 n -∗
      raw_array_span t i (dq1 ⋅ dq2) n.
    Proof.
      iIntros "(%vs & % & Hview1) (%_vs & % & Hview2)".
      iDestruct (raw_array_view_agree with "Hview1 Hview2") as %<-; first naive_solver.
      iDestruct (raw_array_view_combine with "Hview1 Hview2")as "Hview"; first done.
      iExists vs. naive_solver.
    Qed.

    Lemma raw_array_span_append t i dq n1 n2 :
      raw_array_span t i dq n1 -∗
      raw_array_span t (i + n1) dq n2 -∗
      raw_array_span t i dq (n1 + n2).
    Proof.
      iIntros "(%vs1 & % & Hview1) (%vs2 & % & Hview2)".
      iDestruct (raw_array_view_app with "Hview1 Hview2") as "Hview"; first done.
      iExists (vs1 ++ vs2). iSplit; first solve_length. done.
    Qed.

    Lemma raw_array_span_split t i dq n1 n2 n :
      n = n1 + n2 →
      raw_array_span t i dq n -∗
        raw_array_span t i dq n1 ∗
        raw_array_span t (i + n1) dq n2.
    Proof.
      iIntros "% (%vs & % & Hview)".
      iDestruct (raw_array_view_split _ _ _ (take n1 vs) (drop n1 vs) with "Hview") as "(Hview1 & Hview2)"; first rewrite take_drop //.
      iSplitL "Hview1".
      - iExists (take n1 vs). iFrame. iPureIntro.
        rewrite take_length. lia.
      - iExists (drop n1 vs).
        rewrite take_length_le; last lia.
        iFrame. iPureIntro.
        rewrite drop_length. lia.
    Qed.
  End raw_array_span.

  Lemma raw_array_make_spec (sz : Z) v :
    (0 < sz)%Z →
    {{{ True }}}
      raw_array_make #sz v
    {{{ t,
      RET t;
      let sz := Z.to_nat sz in
      raw_array_inv t sz ∗
      raw_array_model t (DfracOwn 1) (replicate sz v)
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    wp_rec. wp_pures.
    iApply wp_fupd. wp_apply (wp_allocN with "[//]"); first done. iIntros "%l (H↦ & Hmeta)".
    iDestruct (big_sepL_lookup _ _ 0 with "Hmeta") as "Hmeta".
    { apply lookup_seq. naive_solver lia. }
    iEval (rewrite loc_add_0) in "Hmeta".
    iApply "HΦ".
    iMod (auth_nat_max_alloc (Z.to_nat sz)) as "(%γ & H●)".
    iDestruct (auth_nat_max_frag_get with "H●") as "#H◯".
    iMod (auth_nat_max_auth_persist with "H●") as "#H●".
    iMod (meta_set _ _ γ raw_array_meta_token with "Hmeta") as "#Hmeta"; first done.
    iSplitR; iExists l, γ; iFrame "∗#"; first auto with lia.
    iSplitR; first done.
    iSplitR; first rewrite replicate_length Nat.add_0_l //.
    iApply (big_sepL_impl with "H↦"). iIntros "!> !> %j %_v % H↦".
    rewrite Nat.add_0_l //.
  Qed.

  Lemma raw_array_get_spec t sz (i : Z) dq :
    (0 ≤ i < sz)%Z →
    <<< raw_array_inv t sz | ∀∀ v, raw_array_mapsto t (Z.to_nat i) dq v >>>
      raw_array_get t #i
    <<< raw_array_mapsto t (Z.to_nat i) dq v | RET v; True >>>.
  Proof.
    iIntros "% !> %Φ (%l & %γ & -> & #Hmeta & % & #H●) HΦ".
    wp_rec. wp_pures.
    iMod "HΦ" as "(%v & (%_l & %_γ & %Heq & #_Hmeta & #H◯ & H↦) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    rewrite Z2Nat.id; last lia. wp_load.
    iApply ("HΦ" with "[H↦] [//]").
    iExists l, γ. iFrame "∗#". iSplit; first done.
    rewrite Z2Nat.id //. lia.
  Qed.

  Lemma raw_array_set_spec t sz i v :
    (0 ≤ i < sz)%Z →
    <<< raw_array_inv t sz | ∀∀ w, raw_array_mapsto t (Z.to_nat i) (DfracOwn 1) w >>>
      raw_array_set t #i v
    <<< raw_array_mapsto t (Z.to_nat i) (DfracOwn 1) v | RET #(); True >>>.
  Proof.
    iIntros "% !> %Φ (%l & %γ & -> & #Hmeta & % & #H●) HΦ".
    wp_rec. wp_pures.
    iMod "HΦ" as "(%w & (%_l & %_γ & %Heq & #_Hmeta & #H◯ & H↦) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    rewrite Z2Nat.id; last lia. wp_store.
    iApply ("HΦ" with "[H↦] [//]").
    iExists l, γ. iFrame "∗#". iSplit; first done.
    rewrite Z2Nat.id //. lia.
  Qed.

  Lemma raw_array_unboxed t sz :
    raw_array_inv t sz -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & % & #H●) //".
  Qed.
End raw_array_G.

#[global] Opaque raw_array_make.
#[global] Opaque raw_array_get.
#[global] Opaque raw_array_set.

#[global] Opaque raw_array_inv.
#[global] Opaque raw_array_mapsto.
#[global] Opaque raw_array_view.
#[global] Opaque raw_array_model.
#[global] Opaque raw_array_span.
