From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.
From caml5.std Require Import
  record3.

Section heapGS.
  Context `{!heapGS Σ}.
  Implicit Types l : loc.
  Implicit Types v w t prev last next : val.

  Notation "t '.(prev)'" := t.(0)%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(data)'" := t.(1)%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(next)'" := t.(2)%E
  ( at level 5
  ) : expr_scope.

  Definition dlchain_prev : val :=
    λ: "t",
      !"t".(prev).
  Definition dlchain_data : val :=
    λ: "t",
      !"t".(data).
  Definition dlchain_next : val :=
    λ: "t",
      !"t".(next).

  Definition dlchain_set_prev : val :=
    λ: "t" "prev",
      "t".(prev) <- "prev".
  Definition dlchain_set_data : val :=
    λ: "t" "data",
      "t".(data) <- "data".
  Definition dlchain_set_next : val :=
    λ: "t" "next",
      "t".(next) <- "next".

  Definition dlchain_singleton : val :=
    λ: "prev" "v" "next",
      record3_make "prev" "v" "next".

  Definition dlchain_advance_backward : val :=
    rec: "dlchain_advance_backward" "t" "i" :=
      if: "i" = #0 then (
        "t"
      ) else (
      "dlchain_advance_backward" (dlchain_prev "t") ("i" - #1)
    ).
  Definition dlchain_advance_forward : val :=
    rec: "dlchain_advance_forward" "t" "i" :=
      if: "i" = #0 then (
        "t"
      ) else (
      "dlchain_advance_forward" (dlchain_next "t") ("i" - #1)
    ).
  Definition dlchain_advance : val :=
    λ: "t" "i",
      if: "i" < #0 then (
        dlchain_advance_backward "t" "i"
      ) else (
        dlchain_advance_forward "t" "i"
      ).

  Definition dlchain_get : val :=
    λ: "t" "i",
      dlchain_data (dlchain_advance "t" "i").
  Definition dlchain_set : val :=
    λ: "t" "i" "v",
      dlchain_set_data (dlchain_advance "t" "i") "v".

  #[local] Definition dlchain_node l dq prev v next :=
    record3_model l dq prev v next.
  Fixpoint dlchain_model t dq prev vs last next : iProp Σ :=
    match vs with
    | [] =>
        ⌜t = next ∧ prev = last⌝
    | v :: vs =>
        ∃ l t',
        ⌜t = #l⌝ ∗
        dlchain_node l dq prev v t' ∗ dlchain_model t' dq t vs last next
    end.

  #[global] Instance dlchain_model_timeless t dq prev vs last next :
    Timeless (dlchain_model t dq prev vs last next).
  Proof.
    revert t prev. induction vs; apply _.
  Qed.
  #[global] Instance dlchain_model_persistent t prev vs last next :
    Persistent (dlchain_model t DfracDiscarded prev vs last next).
  Proof.
    rewrite /Persistent.
    iInduction vs as [| v vs] "IH" forall (t prev); first naive_solver.
    iIntros "(%l & %t' & -> & #Hnode & Hmodel')".
    iDestruct ("IH" with "Hmodel'") as "#?".
    iModIntro. naive_solver.
  Qed.

  #[global] Instance dlchain_model_fractional t prev vs last next :
    Fractional (λ q, dlchain_model t (DfracOwn q) prev vs last next).
  Proof.
    intros q1 q2. iSplit.
    - iInduction vs as [| v vs] "IH" forall (t prev); first done.
      iIntros "(%l & %t' & -> & Hnode & Hmodel')".
      iDestruct (fractional_split_1 with "Hnode") as "(Hnode1 & Hnode2)".
      iDestruct ("IH" with "Hmodel'") as "(Hmodel'1 & Hmodel'2)".
      iSplitL "Hnode1 Hmodel'1"; repeat iExists _; auto with iFrame.
    - iInduction vs as [| v vs] "IH" forall (t prev); first iIntros "(% & _) //".
      iIntros "((%l & %t' & -> & Hnode1 & Hmodel'1) & (%_l & %_t' & %Heq & Hnode2 & Hmodel'2))". injection Heq as <-.
      iDestruct (record3_model_agree with "Hnode1 Hnode2") as %(_ & _ & <-).
      iDestruct (fractional_merge with "Hnode1 Hnode2") as "Hnode".
      iDestruct ("IH" with "[$Hmodel'1 $Hmodel'2]") as "Hmodel'".
      repeat iExists _. auto with iFrame.
  Qed.
  #[global] Instance dlchain_model_as_fractional t q prev vs last next :
    AsFractional (dlchain_model t (DfracOwn q) prev vs last next) (λ q, dlchain_model t (DfracOwn q) prev vs last next) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma dlchain_model_nil t dq prev last next :
    ⌜t = next ∧ prev = last⌝ ⊣⊢
    dlchain_model t dq prev [] last next.
  Proof.
    auto.
  Qed.
  Lemma dlchain_model_nil_1 v prev dq :
    ⊢ dlchain_model v dq prev [] prev v.
  Proof.
    auto.
  Qed.
  Lemma dlchain_model_nil_2 t dq prev last next :
    dlchain_model t dq prev [] last next -∗
    ⌜t = next ∧ prev = last⌝.
  Proof.
    auto.
  Qed.

  Lemma dlchain_model_app_1 dq t1 prev vs1 last1 t2 vs2 last2 next :
    dlchain_model t1 dq prev vs1 last1 t2 -∗
    dlchain_model t2 dq last1 vs2 last2 next -∗
    dlchain_model t1 dq prev (vs1 ++ vs2) last2 next.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t1 prev).
    - iIntros "(-> & ->)". naive_solver.
    - iIntros "(%l1 & %t1' & -> & Hnode1 & Hmodel1') Hmodel2".
      rewrite -app_comm_cons.
      iExists l1, t1'. iFrame. iSplit; first done.
      iApply ("IH" with "Hmodel1' Hmodel2").
  Qed.
  Lemma dlchain_model_app_2 vs1 vs2 t dq prev vs last next :
    vs = vs1 ++ vs2 →
    dlchain_model t dq prev vs last next -∗
      ∃ last' t',
      dlchain_model t dq prev vs1 last' t' ∗
      dlchain_model t' dq last' vs2 last next.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t prev vs); iIntros (->).
    - naive_solver.
    - rewrite -app_comm_cons.
      iIntros "(%l & %t' & -> & Hnode & Hmodel')".
      iDestruct ("IH" with "[//] Hmodel'") as "(%last' & %t'' & Hmodel' & Hmodel'')".
      iExists last', t''. iFrame. iExists l, t'. auto with iFrame.
  Qed.
  Lemma dlchain_model_app t dq prev vs1 vs2 last next :
    ( ∃ last' t',
      dlchain_model t dq prev vs1 last' t' ∗
      dlchain_model t' dq last' vs2 last next
    ) ⊣⊢
    dlchain_model t dq prev (vs1 ++ vs2) last next.
  Proof.
    iSplit.
    - iIntros "(%last' & %t' & Hmodel & Hmodel')".
      iApply (dlchain_model_app_1 with "Hmodel Hmodel'").
    - iApply dlchain_model_app_2; first done.
  Qed.

  Lemma dlchain_model_persist t dq prev vs last next :
    dlchain_model t dq prev vs last next ==∗
    dlchain_model t DfracDiscarded prev vs last next.
  Proof.
    iInduction vs as [| v vs] "IH" forall (t prev); first done.
    iIntros "(%l & %t' & -> & Hnode & Hmodel')".
    iMod (record3_model_persist with "Hnode") as "Hnode".
    iMod ("IH" with "Hmodel'") as "Hmodel'".
    repeat iExists _. naive_solver.
  Qed.

  Lemma dlchain_model_valid t dq prev vs last next :
    0 < length vs →
    dlchain_model t dq prev vs last next -∗
    ⌜✓ dq⌝.
  Proof.
    intros. destruct vs as [| v vs]; first naive_solver lia.
    iIntros "(%l & %t' & -> & Hnode & Hmodel')".
    iApply (record3_model_valid with "Hnode").
  Qed.
  Lemma dlchain_model_combine t prev dq1 vs1 last1 next1 dq2 vs2 last2 next2 :
    length vs1 ≤ length vs2 →
    dlchain_model t dq1 prev vs1 last1 next1 -∗
    dlchain_model t dq2 prev vs2 last2 next2 -∗
      dlchain_model t (dq1 ⋅ dq2) prev vs1 last1 next1 ∗
      dlchain_model next1 dq2 last1 (drop (length vs1) vs2) last2 next2 ∗
      ⌜vs1 = take (length vs1) vs2⌝.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t prev vs2);
      destruct vs2 as [| v2 vs2].
    - iIntros "_ (-> & ->) (-> & ->) //".
    - iIntros "_ (-> & ->) (%l & %t' & -> & Hnode & Hmodel')".
      repeat iSplit; try done. iExists l, t'. auto with iFrame.
    - iIntros "%Hlength". simpl in Hlength. lia.
    - iIntros "%Hlength (%l & %t' & -> & Hnode1 & Hmodel'1) (%_l & %_t' & %Heq & Hnode2 & Hmodel'2)". injection Heq as <-.
      simpl in Hlength. eapply le_S_n in Hlength.
      iDestruct (record3_model_combine with "Hnode1 Hnode2") as "(Hnode & _ & <- & <-)".
      iDestruct ("IH" with "[] Hmodel'1 Hmodel'2") as "(Hmodel' & Hmodel'2 & ->)"; first done.
      iFrame. iSplit; last rewrite /= take_length min_l //.
      iExists l, t'. auto with iFrame.
  Qed.
  Lemma dlchain_model_combine' t prev dq1 vs1 last1 next1 dq2 vs2 last2 next2 :
    length vs1 = length vs2 →
    dlchain_model t dq1 prev vs1 last1 next1 -∗
    dlchain_model t dq2 prev vs2 last2 next2 -∗
      dlchain_model t (dq1 ⋅ dq2) prev vs1 last1 next1 ∗
      ⌜vs1 = vs2 ∧ last1 = last2 ∧ next1 = next2⌝.
  Proof.
    iIntros "%Hlength Hmodel1 Hmodel2".
    iDestruct (dlchain_model_combine with "Hmodel1 Hmodel2") as "($ & Hmodel2 & ->)"; first lia.
    rewrite Hlength take_length min_l; last lia.
    rewrite drop_all. iDestruct "Hmodel2" as %(-> & ->).
    rewrite take_ge //.
  Qed.
  Lemma dlchain_model_valid_2 t prev dq1 vs1 last1 next1 dq2 vs2 last2 next2 :
    0 < length vs1 ≤ length vs2 →
    dlchain_model t dq1 prev vs1 last1 next1 -∗
    dlchain_model t dq2 prev vs2 last2 next2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = take (length vs1) vs2⌝.
  Proof.
    iIntros "% Hmodel1 Hmodel2".
    iDestruct (dlchain_model_combine with "Hmodel1 Hmodel2") as "(Hmodel & _ & %)"; first lia.
    iDestruct (dlchain_model_valid with "Hmodel") as %?; first lia.
    done.
  Qed.
  Lemma dlchain_model_valid_2' t prev dq1 vs1 last1 next1 dq2 vs2 last2 next2 :
    0 < length vs1 →
    length vs1 = length vs2 →
    dlchain_model t dq1 prev vs1 last1 next1 -∗
    dlchain_model t dq2 prev vs2 last2 next2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2 ∧ last1 = last2 ∧ next1 = next2⌝.
  Proof.
    iIntros "% % Hmodel1 Hmodel2".
    iDestruct (dlchain_model_combine' with "Hmodel1 Hmodel2") as "(Hmodel & <- & <- & <-)"; first done.
    iDestruct (dlchain_model_valid with "Hmodel") as %?; done.
  Qed.
  Lemma dlchain_model_agree t prev dq1 vs1 last1 next1 dq2 vs2 last2 next2 :
    length vs1 = length vs2 →
    dlchain_model t dq1 prev vs1 last1 next1 -∗
    dlchain_model t dq2 prev vs2 last2 next2 -∗
    ⌜vs1 = vs2 ∧ last1 = last2 ∧ next1 = next2⌝.
  Proof.
    iIntros "% Hmodel1 Hmodel2".
    iDestruct (dlchain_model_combine' with "Hmodel1 Hmodel2") as "(_ & <- & <- & <-)"; done.
  Qed.
  Lemma dlchain_model_dfrac_ne prev t1 dq1 vs1 last1 next1 t2 dq2 vs2 last2 next2 :
    0 < length vs1 ≤ length vs2 →
    ¬ ✓ (dq1 ⋅ dq2) →
    dlchain_model t1 dq1 prev vs1 last1 next1 -∗
    dlchain_model t2 dq2 prev vs2 last2 next2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    iIntros "% % Hmodel1 Hmodel2" (->).
    iDestruct (dlchain_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
  Qed.
  Lemma dlchain_model_ne prev t1 vs1 last1 next1 t2 dq2 vs2 last2 next2 :
    0 < length vs1 ≤ length vs2 →
    dlchain_model t1 (DfracOwn 1) prev vs1 last1 next1 -∗
    dlchain_model t2 dq2 prev vs2 last2 next2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    intros. iApply dlchain_model_dfrac_ne; [done | intros []%exclusive_l; apply _].
  Qed.
  Lemma dlchain_model_exclusive t prev vs1 last1 next1 vs2 last2 next2 :
    0 < length vs1 ≤ length vs2 →
    dlchain_model t (DfracOwn 1) prev vs1 last1 next1 -∗
    dlchain_model t (DfracOwn 1) prev vs2 last2 next2 -∗
    False.
  Proof.
    iIntros "% Hmodel1 Hmodel2".
    iDestruct (dlchain_model_ne with "Hmodel1 Hmodel2") as %?; naive_solver.
  Qed.

  Lemma dlchain_prev_spec t dq prev vs last next :
    0 < length vs →
    {{{ dlchain_model t dq prev vs last next }}}
      dlchain_prev t
    {{{ RET prev; dlchain_model t dq prev vs last next }}}.
  Proof.
    destruct vs as [| v vs]; [naive_solver lia | intros _].
    iIntros "%Φ (%l & %t' & -> & Hnode & Hmodel') HΦ".
    wp_rec. wp_pures.
    wp_apply (record3_get0_spec with "Hnode"). iIntros "Hnode".
    iApply "HΦ". iExists l, t'. auto with iFrame.
  Qed.
  Lemma dlchain_data_spec t dq prev v vs last next :
    {{{ dlchain_model t dq prev (v :: vs) last next }}}
      dlchain_data t
    {{{ RET v; dlchain_model t dq prev (v :: vs) last next }}}.
  Proof.
    iIntros "%Φ (%l & %t' & -> & Hnode & Hmodel') HΦ".
    wp_rec. wp_pures.
    wp_apply (record3_get1_spec with "Hnode"). iIntros "Hnode".
    iApply "HΦ". iFrame. iExists l, t'. auto with iFrame.
  Qed.
  Lemma dlchain_next_spec t dq prev v vs last next :
    {{{ dlchain_model t dq prev (v :: vs) last next }}}
      dlchain_next t
    {{{ t',
      RET t';
      dlchain_model t dq prev [v] t t' ∗
      dlchain_model t' dq t vs last next
    }}}.
  Proof.
    iIntros "%Φ (%l & %t' & -> & Hnode & Hmodel') HΦ".
    wp_rec. wp_pures.
    wp_apply (record3_get2_spec with "Hnode"). iIntros "Hnode".
    iApply "HΦ". iFrame. iExists l, t'. auto with iFrame.
  Qed.

  Lemma dlchain_set_prev_spec t prev vs last next prev' :
    0 < length vs →
    {{{ dlchain_model t (DfracOwn 1) prev vs last next }}}
      dlchain_set_prev t prev'
    {{{ RET #(); dlchain_model t (DfracOwn 1) prev' vs last next }}}.
  Proof.
    destruct vs as [| v vs]; [naive_solver lia | intros _].
    iIntros "%Φ (%l & %t' & -> & Hnode & Hmodel') HΦ".
    wp_rec. wp_pures.
    wp_apply (record3_set0_spec with "Hnode"). iIntros "Hnode".
    iApply "HΦ". iExists l, t'. auto with iFrame.
  Qed.
  Lemma dlchain_set_data_spec t prev v vs last next w :
    {{{ dlchain_model t (DfracOwn 1) prev (v :: vs) last next }}}
      dlchain_set_data t w
    {{{ RET #(); dlchain_model t (DfracOwn 1) prev (w :: vs) last next }}}.
  Proof.
    iIntros "%Φ (%l & %t' & -> & Hnode & Hmodel') HΦ".
    wp_rec. wp_pures.
    wp_apply (record3_set1_spec with "Hnode"). iIntros "Hnode".
    iApply "HΦ". iExists l, t'. auto with iFrame.
  Qed.
  Lemma dlchain_set_next_spec t prev v vs last next w :
    {{{ dlchain_model t (DfracOwn 1) prev (v :: vs) last next }}}
      dlchain_set_next t w
    {{{ t',
      RET #();
      dlchain_model t (DfracOwn 1) prev [v] t w ∗
      dlchain_model t' (DfracOwn 1) t vs last next
    }}}.
  Proof.
    iIntros "%Φ (%l & %t' & -> & Hnode & Hmodel') HΦ".
    wp_rec. wp_pures.
    wp_apply (record3_set2_spec with "Hnode"). iIntros "Hnode".
    iApply "HΦ". iFrame. iExists l, w. auto with iFrame.
  Qed.

  Lemma dlchain_singleton_spec prev v next :
    {{{ True }}}
      dlchain_singleton prev v next
    {{{ t, RET t; dlchain_model t (DfracOwn 1) prev [v] t next }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec. wp_pures.
    wp_apply (record3_make_spec with "[//]"). iIntros "%l Hl".
    iApply "HΦ". iExists l, next. auto with iFrame.
  Qed.

  Lemma dlchain_unboxed t dq prev v vs last next :
    dlchain_model t dq prev (v :: vs) last next -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "(%l & %_ & -> & _) //".
  Qed.
End heapGS.

#[global] Opaque dlchain_prev.
#[global] Opaque dlchain_data.
#[global] Opaque dlchain_next.
#[global] Opaque dlchain_set_prev.
#[global] Opaque dlchain_set_data.
#[global] Opaque dlchain_set_next.
#[global] Opaque dlchain_singleton.
#[global] Opaque dlchain_advance_backward.
#[global] Opaque dlchain_advance_forward.
#[global] Opaque dlchain_advance.
#[global] Opaque dlchain_get.
#[global] Opaque dlchain_set.

#[global] Opaque dlchain_model.
