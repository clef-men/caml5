From caml5 Require Import
  prelude.
From caml5.common Require Import
  tactics.
From caml5.bi Require Import
  big_op.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.
From caml5.std Require Import
  chunk.

Section heapGS.
  Context `{!heapGS Σ}.
  Implicit Types i n : nat.
  Implicit Types l : loc.
  Implicit Types v t fn acc : val.
  Implicit Types vs : list val.

  Notation "t '.(size)'" := t.(0)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(data)'" := t.(1)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(size)'" := t.(0)%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(data)'" := t.(1)%E
  ( at level 5
  ) : expr_scope.

  Definition array_make : val :=
    λ: "sz" "v",
      let: "t" := chunk_make ("sz" + #1) "v" in
      "t".(size) <- "sz" ;;
      "t".

  Definition array_init : val :=
    λ: "sz" "fn",
      chunk_init ("sz" + #1) (λ: "i",
        if: "i" = #0 then "sz" else "fn" ("i" - #1)
      ).

  Definition array_size : val :=
    λ: "t",
      !"t".(size).

  Definition array_get : val :=
    λ: "t" "i",
      !("t".(data) +ₗ "i").
  Definition array_set : val :=
    λ: "t" "i" "v",
      "t".(data) +ₗ "i" <- "v".

  Definition array_cget : val :=
    λ: "t" "i",
      array_get "t" ("i" `rem` array_size "t").
  Definition array_cset : val :=
    λ: "t" "i" "v",
      array_set "t" ("i" `rem` array_size "t") "v".

  Definition array_foldli : val :=
    λ: "t" "acc" "fn",
      chunk_foldli "t".(data) (array_size "t") "acc" "fn".
  Definition array_foldl : val :=
    λ: "t" "acc" "fn",
      chunk_foldl "t".(data) (array_size "t") "acc" "fn".

  Definition array_foldri : val :=
    λ: "t" "fn" "acc",
      chunk_foldri "t".(data) (array_size "t") "fn" "acc".
  Definition array_foldr : val :=
    λ: "t" "fn" "acc",
      chunk_foldr "t".(data) (array_size "t") "fn" "acc".

  Definition array_iteri : val :=
    λ: "t" "fn",
      chunk_iteri "t".(data) (array_size "t") "fn".
  Definition array_iter : val :=
    λ: "t" "fn",
      chunk_iter "t".(data) (array_size "t") "fn".

  Definition array_mapi : val :=
    λ: "t" "fn",
      array_init (array_size "t") (λ: "i", "fn" "i" (array_get "t" "i")).
  Definition array_map : val :=
    λ: "t" "fn",
      array_mapi "t" (λ: <> "v", "fn" "v").

  Definition array_blit : val :=
    λ: "t" "i" "t'" "i'" "n",
      chunk_copy ("t".(data) +ₗ "i") "n" ("t'".(data) +ₗ "i'").
  Definition array_copy : val :=
    λ: "t" "t'" "i'",
      array_blit "t" #0 "t'" "i'" (array_size "t").

  Definition array_grow : val :=
    λ: "t" "sz",
      let: "t'" := array_make "sz" #() in
      array_copy "t" "t'" #0 ;;
      "t'".
  Definition array_shrink : val :=
    λ: "t" "sz",
      let: "t'" := array_make "sz" #() in
      array_blit "t" "sz" "t'" #0 ;;
      "t'".

  Definition array_clone : val :=
    λ: "t",
      array_grow "t" (array_size "t").

  Section array_inv.
    Definition array_inv t (sz : nat) : iProp Σ :=
      ∃ l, ⌜t = #l⌝ ∗ l.(size) ↦□ #sz.

    #[global] Instance array_inv_persistent t sz :
      Persistent (array_inv t sz).
    Proof.
      apply _.
    Qed.
  End array_inv.

  Section array_model.
    Definition array_model t dq vs : iProp Σ :=
      ∃ l, ⌜t = #l⌝ ∗ l.(size) ↦□ #(length vs) ∗ chunk_model l.(data) dq vs.

    #[global] Instance array_model_timeless t dq vs :
      Timeless (array_model t dq vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_model_persistent t vs :
      Persistent (array_model t DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array_model_fractional t vs :
      Fractional (λ q, array_model t (DfracOwn q) vs).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%l & -> & #Hsz & Hmodel1 & Hmodel2)".
        iSplitL "Hmodel1"; iExists l; auto.
      - iIntros "((%l & -> & #Hsz & Hmodel1) & (%_l & %Heq & _ & Hmodel2))". injection Heq as <-.
        iExists l. iFrame "#". iSplit; first done. iApply chunk_model_fractional. iFrame.
    Qed.
    #[global] Instance array_model_as_fractional t q vs :
      AsFractional (array_model t (DfracOwn q) vs) (λ q, array_model t (DfracOwn q) vs) q.
    Proof.
      split; done || apply _.
    Qed.

    Lemma array_inv_model_valid t sz dq vs :
      array_inv t sz -∗
      array_model t dq vs -∗
      ⌜length vs = sz⌝.
    Proof.
      iIntros "(%l & -> & #Hsz) (%_l & %Heq & #_Hsz & _)". injection Heq as <-.
      iDestruct (mapsto_agree with "Hsz _Hsz") as %[= <-%(inj _)]. done.
    Qed.

    Lemma array_model_valid t dq vs :
      0 < length vs →
      array_model t dq vs -∗
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%l & -> & #Hsz & Hmodel)".
      iApply (chunk_model_valid with "Hmodel"); first done.
    Qed.
    Lemma array_model_combine t dq1 vs1 dq2 vs2 :
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
        array_model t (dq1 ⋅ dq2) vs1 ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "(%l & -> & #Hsz & Hmodel1) (%_l & %Heq & #_Hsz & Hmodel2)". injection Heq as <-.
      iDestruct (mapsto_agree with "Hsz _Hsz") as %[= ?%(inj _)]. iClear "_Hsz".
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(Hmodel & <-)"; first done.
      iSplit; last done. iExists l. auto.
    Qed.
    Lemma array_model_valid_2 t dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (array_model_combine with "Hmodel1 Hmodel2") as "(Hmodel & ->)".
      iDestruct (array_model_valid with "Hmodel") as %?; done.
    Qed.
    Lemma array_model_agree t dq1 vs1 dq2 vs2 :
      array_model t dq1 vs1 -∗
      array_model t dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "Hmodel1 Hmodel2".
      iDestruct (array_model_combine with "Hmodel1 Hmodel2") as "(_ & ->)"; done.
    Qed.
    Lemma array_model_dfrac_ne t1 dq1 vs1 t2 dq2 vs2 :
      0 < length vs1 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array_model t1 dq1 vs1 -∗
      array_model t2 dq2 vs2 -∗
      ⌜t1 ≠ t2⌝.
    Proof.
      iIntros "% % Hmodel1 Hmodel2" (->).
      iDestruct (array_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma array_model_ne t1 vs1 t2 dq2 vs2 :
      0 < length vs1 →
      array_model t1 (DfracOwn 1) vs1 -∗
      array_model t2 dq2 vs2 -∗
      ⌜t1 ≠ t2⌝.
    Proof.
      intros. iApply array_model_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array_model_exclusive t vs1 vs2 :
      0 < length vs1 →
      array_model t (DfracOwn 1) vs1 -∗
      array_model t (DfracOwn 1) vs2 -∗
      False.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (array_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma array_model_persist t dq vs :
      array_model t dq vs ==∗
      array_model t DfracDiscarded vs.
    Proof.
      iIntros "(%l & -> & #Hsz & Hmodel)".
      iMod (chunk_model_persist with "Hmodel") as "Hmodel".
      iExists l. auto.
    Qed.
  End array_model.

  Section array_view.
    Definition array_view t i dq vs : iProp Σ :=
      ∃ l, ⌜t = #l⌝ ∗ chunk_model (l.(data) +ₗ i) dq vs.

    #[global] Instance array_view_timeless t i dq vs :
      Timeless (array_view t i dq vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_view_persistent t i vs :
      Persistent (array_view t i DfracDiscarded vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance array_view_fractional t i vs :
      Fractional (λ q, array_view t i (DfracOwn q) vs).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%l & -> & Hmodel1 & Hmodel2)".
        iSplitL "Hmodel1"; iExists l; auto.
      - iIntros "((%l & -> & Hmodel1) & (%_l & %Heq & Hmodel2))". injection Heq as <-.
        iExists l. iSplit; first done. iApply chunk_model_fractional. iFrame.
    Qed.
    #[global] Instance array_view_as_fractional t i q vs :
      AsFractional (array_view t i (DfracOwn q) vs) (λ q, array_view t i (DfracOwn q) vs) q.
    Proof.
      split; done || apply _.
    Qed.

    Lemma array_view_valid t i dq vs :
      0 < length vs →
      array_view t i dq vs -∗
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%l & -> & Hmodel)".
      iApply (chunk_model_valid with "Hmodel"); first done.
    Qed.
    Lemma array_view_combine t i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array_view t i dq1 vs1 -∗
      array_view t i dq2 vs2 -∗
        array_view t i (dq1 ⋅ dq2) vs1 ∗
        ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% (%l & -> & Hmodel1) (%_l & %Heq & Hmodel2)". injection Heq as <-.
      iDestruct (chunk_model_combine with "Hmodel1 Hmodel2") as "(Hmodel & <-)"; first done.
      iSplit; last done. iExists l. auto.
    Qed.
    Lemma array_view_valid_2 t i dq1 vs1 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_view t i dq1 vs1 -∗
      array_view t i dq2 vs2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (array_view_combine with "Hmodel1 Hmodel2") as "(Hmodel & ->)"; first done.
      iDestruct (array_view_valid with "Hmodel") as %?; done.
    Qed.
    Lemma array_view_agree t i dq1 vs1 dq2 vs2 :
      length vs1 = length vs2 →
      array_view t i dq1 vs1 -∗
      array_view t i dq2 vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      iIntros "% Hmodel1 Hmodel2".
      iDestruct (array_view_combine with "Hmodel1 Hmodel2") as "(_ & ->)"; done.
    Qed.
    Lemma array_view_dfrac_ne t1 i1 dq1 vs1 t2 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array_view t1 i1 dq1 vs1 -∗
      array_view t2 i2 dq2 vs2 -∗
      ⌜t1 ≠ t2 ∨ i1 ≠ i2⌝.
    Proof.
      rewrite -not_and_r. iIntros "% % % Hmodel1 Hmodel2" ((-> & ->)).
      iDestruct (array_view_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma array_view_ne t1 i1 vs1 t2 i2 dq2 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_view t1 i1 (DfracOwn 1) vs1 -∗
      array_view t2 i2 dq2 vs2 -∗
      ⌜t1 ≠ t2 ∨ i1 ≠ i2⌝.
    Proof.
      intros. iApply array_view_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array_view_exclusive t i vs1 vs2 :
      0 < length vs1 →
      length vs1 = length vs2 →
      array_view t i (DfracOwn 1) vs1 -∗
      array_view t i (DfracOwn 1) vs2 -∗
      False.
    Proof.
      iIntros "% % Hmodel1 Hmodel2".
      iDestruct (array_view_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
    Qed.
    Lemma array_view_persist t i dq vs :
      array_view t i dq vs ==∗
      array_view t i DfracDiscarded vs.
    Proof.
      iIntros "(%l & -> & Hmodel)".
      iMod (chunk_model_persist with "Hmodel") as "Hmodel".
      iExists l. auto.
    Qed.

    Lemma array_view_app t i dq vs1 vs2 :
      array_view t i dq vs1 ∗ array_view t (i + length vs1) dq vs2 ⊣⊢
      array_view t i dq (vs1 ++ vs2).
    Proof.
      iSplit.
      - iIntros "((%l & -> & Hmodel1) & (%_l & %Heq & Hmodel2))". injection Heq as <-.
        rewrite Nat2Z.inj_add -loc_add_assoc.
        iDestruct (chunk_model_app_1 with "Hmodel1 Hmodel2") as "Hmodel"; first done.
        iExists l. auto.
      - iIntros "(%l & -> & Hmodel)".
        iDestruct (chunk_model_app with "Hmodel") as "(Hmodel1 & Hmodel2)".
        iSplitL "Hmodel1"; iExists l; first auto.
        rewrite loc_add_assoc -Nat2Z.inj_add. auto.
    Qed.
    Lemma array_view_app_1 t i dq vs1 vs2 sz :
      sz = length vs1 →
      array_view t i dq vs1 -∗
      array_view t (i + sz) dq vs2 -∗
      array_view t i dq (vs1 ++ vs2).
    Proof.
      intros ->. rewrite -array_view_app. auto with iFrame.
    Qed.
    Lemma array_view_app_2 t i dq vs vs1 vs2 :
      vs = vs1 ++ vs2 →
      array_view t i dq vs -∗
        array_view t i dq vs1 ∗
        array_view t (i + length vs1) dq vs2.
    Proof.
      intros ->. rewrite array_view_app //.
    Qed.
  End array_view.

  Section array_span.
    Definition array_span t i dq n : iProp Σ :=
      ∃ vs, ⌜length vs = n⌝ ∗ array_view t i dq vs.

    #[global] Instance array_span_timeless t i dq n :
      Timeless (array_span t i dq n).
    Proof.
      apply _.
    Qed.
    #[global] Instance array_span_persistent t i n :
      Persistent (array_span t i DfracDiscarded n).
    Proof.
      apply _.
    Qed.

    #[global] Instance array_span_fractional t i n :
      Fractional (λ q, array_span t i (DfracOwn q) n).
    Proof.
      intros q1 q2. iSplit.
      - iIntros "(%vs & % & (Hview1 & Hview2))".
        iSplitL "Hview1"; iExists vs; auto.
      - iIntros "((%vs & % & Hview1) & (%_vs & % & Hview2))".
        iDestruct (array_view_agree with "Hview1 Hview2") as %<-; [naive_solver.. |].
        iCombine "Hview1 Hview2" as "Hview".
        iExists vs. auto.
    Qed.
    #[global] Instance array_span_as_fractional t i q vs :
      AsFractional (array_view t i (DfracOwn q) vs) (λ q, array_view t i (DfracOwn q) vs) q.
    Proof.
      apply _.
    Qed.

    Lemma array_span_view_1 t i dq n :
      array_span t i dq n -∗
      ∃ vs, ⌜length vs = n⌝ ∗ array_view t i dq vs.
    Proof.
      done.
    Qed.
    Lemma array_span_view_2 t i dq vs :
      array_view t i dq vs -∗
      array_span t i dq (length vs).
    Proof.
      iIntros "Hview". iExists vs. auto.
    Qed.
    Lemma array_span_view t i dq n :
      array_span t i dq n ⊣⊢
      ∃ vs, ⌜length vs = n⌝ ∗ array_view t i dq vs.
    Proof.
      iSplit.
      - iApply array_span_view_1.
      - iIntros "(%vs & % & Hview)". simplify.
        iApply (array_span_view_2 with "Hview").
    Qed.

    Lemma array_span_valid t i dq n :
      0 < n →
      array_span t i dq n -∗
      ⌜✓ dq⌝.
    Proof.
      iIntros "% (%vs & % & Hview)".
      iDestruct (array_view_valid with "Hview") as %?; naive_solver.
    Qed.
    Lemma array_span_valid_2 t i dq1 n1 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      array_span t i dq1 n1 -∗
      array_span t i dq2 n2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝.
    Proof.
      iIntros (<- ?) "(%vs1 & % & Hview1) (%vs2 & % & Hview2)".
      iDestruct (array_view_valid_2 with "Hview1 Hview2") as "($ & _)"; naive_solver.
    Qed.
    Lemma array_span_combine t i dq1 n1 dq2 n2 :
      n1 = n2 →
      array_span t i dq1 n1 -∗
      array_span t i dq2 n2 -∗
      array_span t i (dq1 ⋅ dq2) n1.
    Proof.
      iIntros "% (%vs & % & Hview1) (%_vs & % & Hview2)".
      iDestruct (array_view_combine with "Hview1 Hview2")as "(Hview & _)"; first naive_solver.
      iExists vs. auto.
    Qed.
    Lemma array_span_dfrac_ne i t1 dq1 n1 t2 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      ¬ ✓ (dq1 ⋅ dq2) →
      array_span t1 i dq1 n1 -∗
      array_span t2 i dq2 n2 -∗
      ⌜t1 ≠ t2⌝.
    Proof.
      iIntros "% % % Hspan1 Hspan2". iIntros (->).
      iDestruct (array_span_valid_2 with "Hspan1 Hspan2") as %?; naive_solver.
    Qed.
    Lemma array_span_ne i n t1 n1 t2 dq2 n2 :
      n1 = n2 →
      0 < n1 →
      array_span t1 i (DfracOwn 1) n1 -∗
      array_span t2 i dq2 n2 -∗
      ⌜t1 ≠ t2⌝.
    Proof.
      intros. iApply array_span_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma array_span_exclusive t i n1 n2 :
      n1 = n2 →
      0 < n1 →
      array_span t i (DfracOwn 1) n1 -∗
      array_span t i (DfracOwn 1) n2 -∗
      False.
    Proof.
      iIntros "% % (%vs1 & % & Hview1) (%vs2 & % & Hview2)".
      iApply (array_view_exclusive with "Hview1 Hview2"); naive_solver.
    Qed.
    Lemma array_span_persist t i dq n :
      array_span t i dq n ==∗
      array_span t i DfracDiscarded n.
    Proof.
      iIntros "(%vs & % & Hview)".
      iExists vs. iSplitR; first done. iApply array_view_persist. done.
    Qed.

    Lemma array_span_app t i dq sz1 sz2 :
      array_span t i dq sz1 ∗ array_span t (i + sz1) dq sz2 ⊣⊢
      array_span t i dq (sz1 + sz2).
    Proof.
      iSplit.
      - iIntros "((%vs1 & % & Hview1) & (%vs2 & % & Hview2))".
        iExists (vs1 ++ vs2). iSplit; first (rewrite app_length; naive_solver).
        iApply (array_view_app_1 with "Hview1 Hview2"); first done.
      - iIntros "(%vs & % & Hview)".
        iDestruct (array_view_app_2 _ _ _ _ (take sz1 vs) (drop sz1 vs) with "Hview") as "(Hview1 & Hview2)"; first rewrite take_drop //.
        iSplitL "Hview1".
        + iExists (take sz1 vs). iFrame. rewrite take_length_le //. lia.
        + iExists (drop sz1 vs). rewrite take_length_le; last lia. iFrame.
          rewrite drop_length. auto with lia.
    Qed.
    Lemma array_span_app_1 t i dq sz1 sz2 :
      array_span t i dq sz1 -∗
      array_span t (i + sz1) dq sz2 -∗
      array_span t i dq (sz1 + sz2).
    Proof.
      rewrite -array_span_app. auto with iFrame.
    Qed.
    Lemma array_span_app_2 t i dq sz sz1 sz2 :
      sz = sz1 + sz2 →
      array_span t i dq sz -∗
        array_span t i dq sz1 ∗
        array_span t (i + sz1) dq sz2.
    Proof.
      intros ->. rewrite array_span_app //.
    Qed.
  End array_span.

  Section array_view_padded.
    Definition array_view_padded t i dq vs pad : iProp Σ :=
      array_view t i dq vs ∗ array_span t (i + length vs) dq pad.
  End array_view_padded.

  Lemma array_make_spec sz v :
    (0 ≤ sz)%Z →
    {{{ True }}}
      array_make #sz v
    {{{ t,
      RET t;
      let sz := Z.to_nat sz in
      array_inv t sz ∗
      array_model t (DfracOwn 1) (replicate sz v)
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    rename sz into _sz. destruct (Z_of_nat_complete _sz) as (sz & ->); first done.
    wp_rec. wp_pures.
    wp_apply (chunk_make_spec with "[//]"); first lia. iIntros "%l (Hmodel & _)".
    wp_pures.
    rewrite Z.add_1_r -Nat2Z.inj_succ !Nat2Z.id.
    iDestruct (chunk_model_cons with "Hmodel") as "(Hsz & Hmodel)".
    iEval (setoid_rewrite <- (loc_add_0 l)) in "Hsz". wp_store.
    iMod (mapsto_persist with "Hsz") as "#Hsz".
    iApply "HΦ". iSplitR.
    - iExists l. auto.
    - iExists l. rewrite replicate_length. auto.
  Qed.

  Lemma array_init_spec Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ [] ∗
      [∗ list] i ∈ seq 0 (Z.to_nat sz), ∀ vs_done,
        ⌜i = length vs_done⌝ -∗
        Ψ vs_done -∗
        WP fn #(i : nat) {{ v, Ψ (vs_done ++ [v]) }}
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "% %Φ (HΨ & Hfn) HΦ".
    rename sz into _sz. destruct (Z_of_nat_complete _sz) as (sz & ->); first done. rewrite Nat2Z.id.
    wp_rec.
    pose Ψ' vs := (
      match vs with
      | [] => Ψ []
      | v :: vs => ⌜v = #sz⌝ ∗ Ψ vs
      end
    )%I.
    iApply wp_fupd. wp_smart_apply (chunk_init_spec Ψ' with "[$HΨ Hfn]"); first lia.
    { rewrite Z.add_1_r -Nat2Z.inj_succ Nat2Z.id (seq_app 1 sz) /=. iSplitR.
      - iIntros (vs_done ->%symmetry%nil_length_inv) "HΨ'".
        wp_pures.
        naive_solver.
      - iApply (big_sepL_mono_strong' with "[] Hfn"); first rewrite !seq_length //. iIntros "!>" (i ? ? ((-> & _)%lookup_seq & (-> & _)%lookup_seq)) "Hfn %vs_done %Hi HΨ'".
        wp_pures.
        rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ /=.
        destruct vs_done as [| v vs_done]; first done.
        iDestruct "HΨ'" as "(-> & HΨ)".
        iApply (wp_wand with "(Hfn [] HΨ)"); first naive_solver. iIntros "%v HΨ".
        naive_solver.
    }
    iIntros "%l %vs (%Hvs & Hmodel & HΨ' & _)".
    destruct vs as [| v vs]; first (simpl in Hvs; lia).
    iDestruct (chunk_model_cons with "Hmodel") as "(Hsz & Hmodel)".
    iMod (mapsto_persist with "Hsz") as "#Hsz". iModIntro.
    iDestruct "HΨ'" as "(-> & HΨ)".
    iApply ("HΦ" $! _ vs). iFrame.
    iSplit. { list_simplifier. auto with lia. }
    iExists l. rewrite loc_add_0. iFrame. iSplit; first done.
    assert (length vs = sz) as -> by (simpl in Hvs; lia). done.
  Qed.
  Lemma array_init_spec' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      Ψ [] ∗
      ∀ i vs_done,
      {{{ ⌜i = length vs_done ∧ i < Z.to_nat sz⌝ ∗ Ψ vs_done }}}
        fn #i
      {{{ v, RET v; Ψ (vs_done ++ [v]) }}}
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "% %Φ (HΨ & #Hfn) HΦ".
    wp_apply (array_init_spec Ψ with "[$HΨ]"); try done.
    iApply big_sepL_intro. iIntros "!> %i %_i %H_i %vs_done % HΨ". apply lookup_seq in H_i as (-> & ?).
    iApply ("Hfn" with "[$HΨ]"); naive_solver.
  Qed.
  Lemma array_init_spec_disentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #(i : nat) {{ Ψ i }}
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ([∗ list] i ↦ v ∈ vs, Ψ i v)
    }}}.
  Proof.
    iIntros "% %Φ Hfn HΦ".
    set (Ψ' vs := ([∗ list] i ↦ v ∈ vs, Ψ i v)%I).
    wp_apply (array_init_spec Ψ' with "[Hfn]"); try done.
    iSplit; first rewrite /Ψ' //.
    iApply (big_sepL_mono with "Hfn"). iIntros "%i %v % Hfn %vs_done -> HΨ'".
    iApply (wp_wand with "Hfn"). iIntros "%v HΨ". iFrame. iSplitL; last done.
    rewrite right_id //.
  Qed.
  Lemma array_init_spec_disentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ∀ i,
      {{{ ⌜i < Z.to_nat sz⌝ }}}
        fn #i
      {{{ v, RET v; Ψ i v }}}
    }}}
      array_init #sz fn
    {{{ t vs,
      RET t ;
      ⌜length vs = Z.to_nat sz⌝ ∗
      array_model t (DfracOwn 1) vs ∗
      ([∗ list] i ↦ v ∈ vs, Ψ i v)
    }}}.
  Proof.
    iIntros "% %Φ #Hfn HΦ".
    wp_apply array_init_spec_disentangled; try done.
    iApply big_sepL_intro. iIntros "!> %i %_i %Hlookup".
    apply lookup_seq in Hlookup as (-> & ?).
    iApply ("Hfn" with "[//]"). auto.
  Qed.

  Lemma array_get_spec t (i : Z) dq vs v E :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{
      array_model t dq vs
    }}}
      array_get t #i @ E
    {{{
      RET v;
      array_model t dq vs
    }}}.
  Proof.
    iIntros "% % %Φ (%l & -> & #Hsz & Hmodel) HΦ".
    wp_rec.
    wp_smart_apply (chunk_get_spec with "Hmodel"); [done.. |]. iIntros "Hmodel".
    iApply "HΦ". iExists l. auto.
  Qed.
  Lemma array_get_spec' t (j : nat) dq vs (i : Z) v E :
    (j ≤ i)%Z →
    vs !! Z.to_nat (i - j) = Some v →
    {{{
      array_view t j dq vs
    }}}
      array_get t #i @ E
    {{{
      RET v;
      array_view t j dq vs
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ (%l & -> & Hmodel) HΦ".
    destruct (Z_of_nat_complete (i - j)) as (k & Hk); first lia.
    assert (i = j + k)%Z as -> by lia.
    rewrite Z.add_simpl_l in Hlookup.
    wp_rec. wp_pures.
    rewrite -loc_add_assoc.
    wp_apply (chunk_get_spec with "Hmodel"); [lia | done |]. iIntros "Hmodel".
    iApply "HΦ". iExists l. auto.
  Qed.

  Lemma array_size_spec t sz :
    {{{
      array_inv t sz
    }}}
      array_size t
    {{{
      RET #sz; True
    }}}.
  Proof.
    iIntros "%Φ (%l & -> & #Hsz) HΦ".
    wp_rec. wp_pures. wp_load.
    iApply ("HΦ" with "[//]").
  Qed.
  Lemma array_size_spec' t dq vs :
    {{{
      array_model t dq vs
    }}}
      array_size t
    {{{
      RET #(length vs); True
    }}}.
  Proof.
    iIntros "%Φ (%l & -> & #Hsz & Hmodel) HΦ".
    wp_rec. wp_pures. wp_load.
    iApply ("HΦ" with "[//]").
  Qed.

  Lemma array_set_spec t (i : Z) vs v E :
    (0 ≤ i < length vs)%Z →
    {{{
      array_model t (DfracOwn 1) vs
    }}}
      array_set t #i v @ E
    {{{
      RET #();
      array_model t (DfracOwn 1) (<[Z.to_nat i := v]> vs)
    }}}.
  Proof.
    iIntros "% %Φ (%l & -> & #Hsz & Hmodel) HΦ".
    wp_rec.
    wp_smart_apply (chunk_set_spec with "Hmodel"); first done. iIntros "Hmodel".
    iApply "HΦ". iExists l. rewrite insert_length. auto.
  Qed.
  Lemma array_set_spec' t (j : nat) vs (i : Z) v E :
    (j ≤ i < j + length vs)%Z →
    {{{
      array_view t j (DfracOwn 1) vs
    }}}
      array_set t #i v @ E
    {{{
      RET #();
      array_view t j (DfracOwn 1) (<[Z.to_nat (i - j) := v]> vs)
    }}}.
  Proof.
    iIntros "% %Φ (%l & -> & Hmodel) HΦ".
    destruct (Z_of_nat_complete (i - j)) as (k & Hk); first lia.
    assert (i = j + k)%Z as -> by lia.
    wp_rec. wp_pures.
    rewrite -loc_add_assoc.
    wp_smart_apply (chunk_set_spec with "Hmodel"); first lia. iIntros "Hmodel".
    iApply "HΦ". iExists l. rewrite Z.add_simpl_l. auto.
  Qed.

  Lemma array_foldli_spec Ψ t dq vs acc fn :
    {{{
      array_model t dq vs ∗
      Ψ [] acc ∗
      [∗ list] i ↦ v ∈ vs, ∀ acc,
        Ψ (take i vs) acc -∗
        WP fn acc #i (v : val) {{ acc', Ψ (take i vs ++ [v]) acc' }}
    }}}
      array_foldli t acc fn
    {{{ acc',
      RET acc';
      array_model t dq vs ∗
      Ψ vs acc'
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_foldli_spec Ψ with "[$Hmodel $HΨ $Hfn]"); first done. iIntros "%acc' (Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.
  Lemma array_foldli_spec' Ψ t dq vs acc fn :
    {{{
      array_model t dq vs ∗
      Ψ [] acc ∗
      ∀ acc i v,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ (take i vs) acc }}}
        fn acc #i v
      {{{ acc', RET acc'; Ψ (take i vs ++ [v]) acc' }}}
    }}}
      array_foldli t acc fn
    {{{ acc',
      RET acc';
      array_model t dq vs ∗
      Ψ vs acc'
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_foldli_spec' Ψ with "[$Hmodel $HΨ $Hfn]"); first done. iIntros "%acc' (Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.

  Lemma array_foldl_spec Ψ t dq vs acc fn :
    {{{
      array_model t dq vs ∗
      Ψ [] acc ∗
      [∗ list] i ↦ v ∈ vs, ∀ acc,
        Ψ (take i vs) acc -∗
        WP fn acc (v : val) {{ acc', Ψ (take i vs ++ [v]) acc' }}
    }}}
      array_foldl t acc fn
    {{{ acc',
      RET acc';
      array_model t dq vs ∗
      Ψ vs acc'
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_foldl_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done. iIntros "%acc' (Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.
  Lemma array_foldl_spec' Ψ t dq vs acc fn :
    {{{
      array_model t dq vs ∗
      Ψ [] acc ∗
      ∀ i v acc,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ (take i vs) acc }}}
        fn acc v
      {{{ acc', RET acc'; Ψ (take i vs ++ [v]) acc' }}}
    }}}
      array_foldl t acc fn
    {{{ acc',
      RET acc';
      array_model t dq vs ∗
      Ψ vs acc'
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_foldl_spec' Ψ with "[$Hmodel $HΨ Hfn]"); try done. iIntros "%acc' (Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.

  Lemma array_foldri_spec Ψ t dq vs acc fn :
    {{{
      array_model t dq vs ∗
      Ψ acc [] ∗
      [∗ list] i ↦ v ∈ vs, ∀ acc,
        Ψ acc (drop (S i) vs) -∗
        WP fn #i (v : val) acc {{ acc', Ψ acc' (v :: drop (S i) vs) }}
    }}}
      array_foldri t fn acc
    {{{ acc',
      RET acc';
      array_model t dq vs ∗
      Ψ acc' vs
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_foldri_spec Ψ with "[$Hmodel $HΨ $Hfn]"); first done. iIntros "%acc' (Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.
  Lemma array_foldri_spec' Ψ t dq vs acc fn :
    {{{
      array_model t dq vs ∗
      Ψ acc [] ∗
      ∀ acc i v,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ acc (drop (S i) vs) }}}
        fn #i v acc
      {{{ acc', RET acc'; Ψ acc' (v :: drop (S i) vs) }}}
    }}}
      array_foldri t fn acc
    {{{ acc',
      RET acc';
      array_model t dq vs ∗
      Ψ acc' vs
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_foldri_spec' Ψ with "[$Hmodel $HΨ $Hfn]"); first done. iIntros "%acc' (Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.

  Lemma array_foldr_spec Ψ t dq vs acc fn :
    {{{
      array_model t dq vs ∗
      Ψ acc [] ∗
      [∗ list] i ↦ v ∈ vs, ∀ acc,
        Ψ acc (drop (S i) vs) -∗
        WP fn (v : val) acc {{ acc', Ψ acc' (v :: drop (S i) vs) }}
    }}}
      array_foldr t fn acc
    {{{ acc',
      RET acc';
      array_model t dq vs ∗
      Ψ acc' vs
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_foldr_spec Ψ with "[$Hmodel $HΨ $Hfn]"); first done. iIntros "%acc' (Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.
  Lemma array_foldr_spec' Ψ t dq vs acc fn :
    {{{
      array_model t dq vs ∗
      Ψ acc [] ∗
      ∀ i v acc,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ acc (drop (S i) vs) }}}
        fn v acc
      {{{ acc', RET acc'; Ψ acc' (v :: drop (S i) vs) }}}
    }}}
      array_foldr t fn acc
    {{{ acc',
      RET acc';
      array_model t dq vs ∗
      Ψ acc' vs
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_foldr_spec' Ψ with "[$Hmodel $HΨ $Hfn]"); first done. iIntros "%acc' (Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.

  Lemma array_iteri_spec Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      Ψ [] ∗
      [∗ list] i ↦ v ∈ vs,
        Ψ (take i vs) -∗
        WP fn #i (v : val) {{ _, Ψ (take i vs ++ [v]) }}
    }}}
      array_iteri t fn
    {{{
      RET #();
      array_model t dq vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_iteri_spec Ψ with "[$Hmodel $HΨ $Hfn]"); first done. iIntros "(Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.
  Lemma array_iteri_spec' Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      Ψ [] ∗
      ∀ i v,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ (take i vs) }}}
        fn #i v
      {{{ w, RET w; Ψ (take i vs ++ [v]) }}}
    }}}
      array_iteri t fn
    {{{
      RET #();
      array_model t dq vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_iteri_spec' Ψ with "[$Hmodel $HΨ $Hfn]"); first done. iIntros "(Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.
  Lemma array_iteri_spec_disentangled Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      [∗ list] i ↦ v ∈ vs,
        WP fn #i (v : val) {{ _, Ψ i v }}
    }}}
      array_iteri t fn
    {{{
      RET #();
      array_model t dq vs ∗
      [∗ list] i ↦ v ∈ vs, Ψ i v
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_iteri_spec_disentangled Ψ with "[$Hmodel $Hfn]"); first done. iIntros "(Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.
  Lemma array_iteri_spec_disentangled' Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      ∀ i v,
      {{{ ⌜vs !! i = Some v⌝ }}}
        fn #i v
      {{{ w, RET w; Ψ i v }}}
    }}}
      array_iteri t fn
    {{{
      RET #();
      array_model t dq vs ∗
      [∗ list] i ↦ v ∈ vs, Ψ i v
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_iteri_spec_disentangled' Ψ with "[$Hmodel $Hfn]"); first done. iIntros "(Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.

  Lemma array_iter_spec Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      Ψ [] ∗
      [∗ list] i ↦ v ∈ vs,
        Ψ (take i vs) -∗
        WP fn (v : val) {{ _, Ψ (take i vs ++ [v]) }}
    }}}
      array_iter t fn
    {{{
      RET #();
      array_model t dq vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_iter_spec Ψ with "[$Hmodel $HΨ $Hfn]"); first done. iIntros "(Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.
  Lemma array_iter_spec' Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      Ψ [] ∗
      ∀ i v,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ (take i vs) }}}
        fn v
      {{{ w, RET w; Ψ (take i vs ++ [v]) }}}
    }}}
      array_iter t fn
    {{{
      RET #();
      array_model t dq vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_iter_spec' Ψ with "[$Hmodel $HΨ $Hfn]"); first done. iIntros "(Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.
  Lemma array_iter_spec_disentangled Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      [∗ list] v ∈ vs,
        WP fn (v : val) {{ _, Ψ v }}
    }}}
      array_iter t fn
    {{{
      RET #();
      array_model t dq vs ∗
      [∗ list] v ∈ vs, Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_iter_spec_disentangled Ψ with "[$Hmodel $Hfn]"); first done. iIntros "(Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.
  Lemma array_iter_spec_disentangled' Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      ∀ v,
      {{{ ⌜v ∈ vs⌝ }}}
        fn v
      {{{ w, RET w; Ψ v }}}
    }}}
      array_iter t fn
    {{{
      RET #();
      array_model t dq vs ∗
      [∗ list] v ∈ vs, Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((%l & -> & #Hsz & Hmodel) & Hfn) HΦ".
    wp_rec.
    wp_smart_apply array_size_spec; first (iExists l; auto). iIntros "_".
    wp_smart_apply (chunk_iter_spec_disentangled' Ψ with "[$Hmodel $Hfn]"); first done. iIntros "(Hmodel & HΨ)".
    iApply "HΦ". iFrame. iExists l. auto.
  Qed.

  Lemma array_mapi_spec Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      Ψ [] [] ∗
      [∗ list] i ↦ v ∈ vs, ∀ ws,
        ⌜length ws = i⌝ -∗
        Ψ (take i vs) ws -∗
        WP fn #i (v : val) {{ w, Ψ (take i vs ++ [v]) (ws ++ [w]) }}
    }}}
      array_mapi t fn
    {{{ t' ws,
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      Ψ vs ws
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    pose Ψ' ws := (
      array_model t dq vs ∗
      Ψ (take (length ws) vs) ws
    )%I.
    wp_smart_apply (array_size_spec with "[#]").
    { iDestruct "Hmodel" as "(%l & -> & #Hsz & _)". iExists l. auto. }
    iIntros "_".
    wp_smart_apply (array_init_spec Ψ' with "[$Hmodel $HΨ Hfn]"); first lia.
    { rewrite Nat2Z.id.
      iApply (big_sepL_seq_index vs); first naive_solver.
      iApply (big_sepL_mono with "Hfn"). iIntros "%i %v %Hlookup Hfn %ws -> (Hmodel & HΨ)".
      wp_smart_apply (array_get_spec with "Hmodel"); [lia | rewrite Nat2Z.id // |]. iIntros "Hmodel".
      iApply (wp_wand with "(Hfn [//] HΨ)"). iIntros "%w HΨ".
      rewrite /Ψ' app_length /= Nat.add_1_r (take_S_r _ _ v); auto with iFrame.
    }
    iIntros "%t' %ws (%Hws & Hmodel' & (Hmodel & HΨ))".
    rewrite Hws Nat2Z.id firstn_all.
    iApply ("HΦ" with "[$Hmodel $Hmodel' $HΨ]").
  Qed.
  Lemma array_mapi_spec' Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      Ψ [] [] ∗
      ∀ i v ws,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ (take i vs) ws }}}
        fn #i v
      {{{ w, RET w; Ψ (take i vs ++ [v]) (ws ++ [w]) }}}
    }}}
      array_mapi t fn
    {{{ t' ws,
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      Ψ vs ws
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_apply (array_mapi_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v % %ws % HΨ".
    wp_apply ("Hfn" with "[$HΨ //]"). naive_solver.
  Qed.
  Lemma array_mapi_spec_disentangled Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      [∗ list] i ↦ v ∈ vs,
        WP fn #i (v : val) {{ w, Ψ i v w }}
    }}}
      array_mapi t fn
    {{{ t' ws,
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      [∗ list] i ↦ v; w ∈ vs; ws, Ψ i v w
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    set (Ψ' vs ws := ([∗ list] i ↦ v; w ∈ vs; ws, Ψ i v w)%I).
    wp_apply (array_mapi_spec Ψ' with "[$Hmodel Hfn]"); try done.
    iSplit; first rewrite /Ψ' //.
    iApply (big_sepL_mono with "Hfn"). iIntros "%i %v %Hlookup Hfn %ws % HΨ'".
    iApply (wp_wand with "Hfn"). iIntros "%w HΨ". iFrame. iSplitL; last done.
    rewrite right_id take_length_le //. apply lookup_lt_Some in Hlookup. lia.
  Qed.
  Lemma array_mapi_spec_disentangled' Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      ∀ i v,
      {{{ ⌜vs !! i = Some v⌝ }}}
        fn #i v
      {{{ w, RET w; Ψ i v w }}}
    }}}
      array_mapi t fn
    {{{ t' ws,
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      [∗ list] i ↦ v; w ∈ vs; ws, Ψ i v w
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp_apply (array_mapi_spec_disentangled Ψ with "[$Hmodel Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v %".
    iApply ("Hfn" with "[//]"). naive_solver.
  Qed.

  Lemma array_map_spec Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      Ψ [] [] ∗
      [∗ list] i ↦ v ∈ vs, ∀ ws,
        Ψ (take i vs) ws -∗
        WP fn (v : val) {{ w, Ψ (take i vs ++ [v]) (ws ++ [w]) }}
    }}}
      array_map t fn
    {{{ t' ws,
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      Ψ vs ws
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (array_mapi_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply (big_sepL_mono with "Hfn"). clear. iIntros "%i %v % Hfn %w % HΨ".
    wp_smart_apply ("Hfn" with "HΨ").
  Qed.
  Lemma array_map_spec' Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      Ψ [] [] ∗
      ∀ i v ws,
      {{{ ⌜vs !! i = Some v⌝ ∗ Ψ (take i vs) ws }}}
        fn v
      {{{ w, RET w; Ψ (take i vs ++ [v]) (ws ++ [w]) }}}
    }}}
      array_map t fn
    {{{ t' ws,
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      Ψ vs ws
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & HΨ & #Hfn) HΦ".
    wp_apply (array_map_spec Ψ with "[$Hmodel $HΨ Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v % %w HΨ".
    wp_apply ("Hfn" with "[$HΨ //]"). naive_solver.
  Qed.
  Lemma array_map_spec_disentangled Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      [∗ list] v ∈ vs,
        WP fn (v : val) {{ Ψ v }}
    }}}
      array_map t fn
    {{{ t' ws,
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      [∗ list] v; w ∈ vs; ws, Ψ v w
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    set (Ψ' vs ws := ([∗ list] v; w ∈ vs; ws, Ψ v w)%I).
    wp_apply (array_map_spec Ψ' with "[$Hmodel Hfn]"); try done.
    iSplit; first rewrite /Ψ' //.
    iApply (big_sepL_mono with "Hfn"). iIntros "%i %v % Hfn %ws HΨ'".
    iApply (wp_wand with "Hfn"). iIntros "%w HΨ". iFrame. done.
  Qed.
  Lemma array_map_spec_disentangled' Ψ t dq vs fn :
    {{{
      array_model t dq vs ∗
      ∀ v,
      {{{ ⌜v ∈ vs⌝ }}}
        fn v
      {{{ w, RET w; Ψ v w }}}
    }}}
      array_map t fn
    {{{ t' ws,
      RET t';
      array_model t dq vs ∗
      array_model t' (DfracOwn 1) ws ∗
      [∗ list] v; w ∈ vs; ws, Ψ v w
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp_apply (array_map_spec_disentangled Ψ with "[$Hmodel Hfn]"); try done.
    iApply big_sepL_intro. clear. iIntros "!> %i %v %".
    iApply "Hfn"; last auto. rewrite elem_of_list_lookup. naive_solver.
  Qed.

  Lemma array_unboxed t sz :
    array_inv t sz -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "(%l & -> & #Hsz) //".
  Qed.
End heapGS.

#[global] Opaque array_make.
#[global] Opaque array_init.
#[global] Opaque array_size.
#[global] Opaque array_get.
#[global] Opaque array_set.
#[global] Opaque array_cget.
#[global] Opaque array_cset.
#[global] Opaque array_foldli.
#[global] Opaque array_foldl.
#[global] Opaque array_foldri.
#[global] Opaque array_foldr.
#[global] Opaque array_iteri.
#[global] Opaque array_iter.
#[global] Opaque array_mapi.
#[global] Opaque array_map.
#[global] Opaque array_blit.
#[global] Opaque array_copy.
#[global] Opaque array_grow.
#[global] Opaque array_shrink.
#[global] Opaque array_clone.

#[global] Opaque array_inv.
#[global] Opaque array_model.
#[global] Opaque array_view.
#[global] Opaque array_span.
