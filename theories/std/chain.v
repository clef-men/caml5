From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.
From caml5.std Require Import
  record_two.

Section heapGS.
  Context `{!heapGS Σ}.
  Implicit Types l : loc.
  Implicit Types v w next hd tl t : val.

  Notation "t '.(head)'" := (t.0)%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(tail)'" := (t.1)%E
  ( at level 5
  ) : expr_scope.

  Definition chain_cons : val :=
    record_two_make.

  Definition chain_head : val :=
    λ: "t",
      !"t".(head).
  Definition chain_tail : val :=
    λ: "t",
      !"t".(tail).

  Definition chain_set_head : val :=
    λ: "t" "v",
      "t".(head) <- "v".
  Definition chain_set_tail : val :=
    λ: "t" "v",
      "t".(tail) <- "v".

  Definition chain_advance : val :=
    rec: "chain_advance" "t" "i" :=
      if: "i" = #0 then (
        "t"
      ) else (
        "chain_advance" (chain_tail "t") ("i" - #1)
      ).

  Definition chain_get : val :=
    λ: "t" "i",
      chain_head (chain_advance "t" "i").
  Definition chain_set : val :=
    λ: "t" "i" "v",
      chain_set_head (chain_advance "t" "i") "v".

  #[local] Definition chain_cell l dq hd tl :=
    record_two_model l dq hd tl.
  Fixpoint chain_model t dq vs next : iProp Σ :=
    match vs with
    | [] =>
        ⌜t = next⌝
    | v :: vs =>
        ∃ l t',
        ⌜t = #l⌝ ∗
        chain_cell l dq v t' ∗ chain_model t' dq vs next
    end.

  Lemma chain_model_unboxed t dq v vs next :
    chain_model t dq (v :: vs) next -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "(%l & %_ & -> & _) //".
  Qed.

  #[global] Instance chain_model_timeless t dq vs next :
    Timeless (chain_model t dq vs next).
  Proof.
    revert t. induction vs; apply _.
  Qed.
  #[global] Instance chain_model_persistent t vs next :
    Persistent (chain_model t DfracDiscarded vs next).
  Proof.
    rewrite /Persistent.
    iInduction vs as [| v vs] "IH" forall (t); first naive_solver.
    iIntros "(%l & %t' & -> & #Hcell & Hmodel')".
    iDestruct ("IH" with "Hmodel'") as "#?".
    iModIntro. naive_solver.
  Qed.

  #[global] Instance chain_model_fractional t vs next :
    Fractional (λ q, chain_model t (DfracOwn q) vs next).
  Proof.
    intros q1 q2. iSplit.
    - iInduction vs as [| v vs] "IH" forall (t); first done.
      iIntros "(%l & %t' & -> & Hcell & Hmodel')".
      iDestruct (fractional_split_1 with "Hcell") as "(Hcell1 & Hcell2)".
      iDestruct ("IH" with "Hmodel'") as "(Hmodel'1 & Hmodel'2)".
      iSplitL "Hcell1 Hmodel'1"; repeat iExists _; auto with iFrame.
    - iInduction vs as [| v vs] "IH" forall (t); first iIntros "(-> & _) //".
      iIntros "((%l & %t' & -> & Hcell1 & Hmodel'1) & (%_l & %_t' & %Heq & Hcell2 & Hmodel'2))". injection Heq as <-.
      iDestruct (record_two_model_agree with "Hcell1 Hcell2") as %(_ & <-).
      iDestruct (fractional_merge with "Hcell1 Hcell2") as "Hcell".
      iDestruct ("IH" with "[$Hmodel'1 $Hmodel'2]") as "Hmodel'".
      repeat iExists _. auto with iFrame.
  Qed.
  #[global] Instance chain_model_as_fractional t q vs next :
    AsFractional (chain_model t (DfracOwn q) vs next) (λ q, chain_model t (DfracOwn q) vs next) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma chain_model_nil t dq next :
    ⌜t = next⌝ ⊣⊢
    chain_model t dq [] next.
  Proof.
    auto.
  Qed.
  Lemma chain_model_nil_1 v dq :
    ⊢ chain_model v dq [] v.
  Proof.
    auto.
  Qed.
  Lemma chain_model_nil_2 t dq next :
    chain_model t dq [] next -∗
    ⌜t = next⌝.
  Proof.
    auto.
  Qed.

  Lemma chain_model_app_1 dq t1 vs1 t2 vs2 next :
    chain_model t1 dq vs1 t2 -∗
    chain_model t2 dq vs2 next -∗
    chain_model t1 dq (vs1 ++ vs2) next.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t1).
    - iIntros "->". naive_solver.
    - iIntros "(%l1 & %t1' & -> & Hcell1 & Hmodel1') Hmodel2".
      rewrite -app_comm_cons.
      iExists l1, t1'. iFrame. iSplit; first done.
      iApply ("IH" with "Hmodel1' Hmodel2").
  Qed.
  Lemma chain_model_app_2 vs1 vs2 t dq vs next :
    vs = vs1 ++ vs2 →
    chain_model t dq vs next -∗
      ∃ t',
      chain_model t dq vs1 t' ∗
      chain_model t' dq vs2 next.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t vs); iIntros (->).
    - naive_solver.
    - rewrite -app_comm_cons.
      iIntros "(%l & %t' & -> & Hcell & Hmodel')".
      iDestruct ("IH" with "[//] Hmodel'") as "(%t'' & Hmodel' & Hmodel'')".
      iExists t''. iFrame. iExists l, t'. auto with iFrame.
  Qed.
  Lemma chain_model_app t dq vs1 vs2 next :
    (∃ t', chain_model t dq vs1 t' ∗ chain_model t' dq vs2 next) ⊣⊢
    chain_model t dq (vs1 ++ vs2) next.
  Proof.
    iSplit.
    - iIntros "(%t' & Hmodel & Hmodel')".
      iApply (chain_model_app_1 with "Hmodel Hmodel'").
    - iApply chain_model_app_2; first done.
  Qed.

  Lemma chain_model_persist t dq vs next :
    chain_model t dq vs next ==∗
    chain_model t DfracDiscarded vs next.
  Proof.
    iInduction vs as [| v vs] "IH" forall (t); first done.
    iIntros "(%l & %t' & -> & Hcell & Hmodel')".
    iMod (record_two_model_persist with "Hcell") as "Hcell".
    iMod ("IH" with "Hmodel'") as "Hmodel'".
    repeat iExists _. naive_solver.
  Qed.

  Lemma chain_model_valid t dq vs next :
    0 < length vs →
    chain_model t dq vs next -∗
    ⌜✓ dq⌝.
  Proof.
    intros. destruct vs as [| v vs]; first naive_solver lia.
    iIntros "(%l & %t' & -> & Hcell & Hmodel')".
    iApply (record_two_model_valid with "Hcell").
  Qed.
  Lemma chain_model_combine t dq1 vs1 next1 dq2 vs2 next2 :
    length vs1 ≤ length vs2 →
    chain_model t dq1 vs1 next1 -∗
    chain_model t dq2 vs2 next2 -∗
      chain_model t (dq1 ⋅ dq2) vs1 next1 ∗
      chain_model next1 dq2 (drop (length vs1) vs2) next2 ∗
      ⌜vs1 = take (length vs1) vs2⌝.
  Proof.
    iInduction vs1 as [| v1 vs1] "IH" forall (t vs2);
      destruct vs2 as [| v2 vs2].
    - iIntros "_ -> -> //".
    - iIntros "_ -> (%l & %t' & -> & Hcell & Hmodel')".
      repeat iSplit; try done. iExists l, t'. auto with iFrame.
    - iIntros "%Hlength". simpl in Hlength. lia.
    - iIntros "%Hlength (%l & %t' & -> & Hcell1 & Hmodel'1) (%_l & %_t' & %Heq & Hcell2 & Hmodel'2)". injection Heq as <-.
      simpl in Hlength. eapply le_S_n in Hlength.
      iDestruct (record_two_model_combine with "Hcell1 Hcell2") as "(Hcell & <- & <-)".
      iDestruct ("IH" with "[] Hmodel'1 Hmodel'2") as "(Hmodel' & Hmodel'2 & ->)"; first done.
      iFrame. iSplit; last rewrite /= take_length min_l //.
      iExists l, t'. auto with iFrame.
  Qed.
  Lemma chain_model_combine' t dq1 vs1 next1 dq2 vs2 next2 :
    length vs1 = length vs2 →
    chain_model t dq1 vs1 next1 -∗
    chain_model t dq2 vs2 next2 -∗
      chain_model t (dq1 ⋅ dq2) vs1 next1 ∗
      ⌜vs1 = vs2 ∧ next1 = next2⌝.
  Proof.
    iIntros "%Hlength Hmodel1 Hmodel2".
    iDestruct (chain_model_combine with "Hmodel1 Hmodel2") as "($ & Hmodel2 & ->)"; first lia.
    rewrite Hlength take_length min_l; last lia.
    rewrite drop_all. iDestruct "Hmodel2" as %->.
    rewrite take_ge //.
  Qed.
  Lemma chain_model_valid_2 t dq1 vs1 next1 dq2 vs2 next2 :
    0 < length vs1 ≤ length vs2 →
    chain_model t dq1 vs1 next1 -∗
    chain_model t dq2 vs2 next2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = take (length vs1) vs2⌝.
  Proof.
    iIntros "% Hmodel1 Hmodel2".
    iDestruct (chain_model_combine with "Hmodel1 Hmodel2") as "(Hmodel & _ & %)"; first lia.
    iDestruct (chain_model_valid with "Hmodel") as %?; first lia.
    done.
  Qed.
  Lemma chain_model_valid_2' t dq1 vs1 next1 dq2 vs2 next2 :
    0 < length vs1 →
    length vs1 = length vs2 →
    chain_model t dq1 vs1 next1 -∗
    chain_model t dq2 vs2 next2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2 ∧ next1 = next2⌝.
  Proof.
    iIntros "% % Hmodel1 Hmodel2".
    iDestruct (chain_model_combine' with "Hmodel1 Hmodel2") as "(Hmodel & <- & <-)"; first done.
    iDestruct (chain_model_valid with "Hmodel") as %?; done.
  Qed.
  Lemma chain_model_agree t dq1 vs1 next1 dq2 vs2 next2 :
    length vs1 = length vs2 →
    chain_model t dq1 vs1 next1 -∗
    chain_model t dq2 vs2 next2 -∗
    ⌜vs1 = vs2 ∧ next1 = next2⌝.
  Proof.
    iIntros "% Hmodel1 Hmodel2".
    iDestruct (chain_model_combine' with "Hmodel1 Hmodel2") as "(_ & <- & <-)"; done.
  Qed.
  Lemma chain_model_dfrac_ne t1 dq1 vs1 next1 t2 dq2 vs2 next2 :
    0 < length vs1 ≤ length vs2 →
    ¬ ✓ (dq1 ⋅ dq2) →
    chain_model t1 dq1 vs1 next1 -∗
    chain_model t2 dq2 vs2 next2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    iIntros "% % Hmodel1 Hmodel2" (->).
    iDestruct (chain_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
  Qed.
  Lemma chain_model_ne t1 vs1 next1 t2 dq2 vs2 next2 :
    0 < length vs1 ≤ length vs2 →
    chain_model t1 (DfracOwn 1) vs1 next1 -∗
    chain_model t2 dq2 vs2 next2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    intros. iApply chain_model_dfrac_ne; [done | intros []%exclusive_l; apply _].
  Qed.
  Lemma chain_model_exclusive t vs1 next1 vs2 next2 :
    0 < length vs1 ≤ length vs2 →
    chain_model t (DfracOwn 1) vs1 next1 -∗
    chain_model t (DfracOwn 1) vs2 next2 -∗
    False.
  Proof.
    iIntros "% Hmodel1 Hmodel2".
    iDestruct (chain_model_ne with "Hmodel1 Hmodel2") as %?; naive_solver.
  Qed.

  #[local] Lemma mapsto_dfrac_relax dq l v :
    ✓ dq →
    l ↦ v ==∗
    l ↦{dq} v.
  Proof.
    iIntros "%Hdq H↦". destruct dq as [q1 | | q1].
    - destruct (decide (q1 < 1)%Qp) as [Hq1 | Hq1].
      + apply Qp.lt_sum in Hq1 as (q2 & ->).
        iDestruct (fractional_split with "H↦") as "(H↦1 & _)". done.
      + apply dfrac_valid_own, Qp.le_lteq in Hdq as [| ->]; done.
    - iApply (mapsto_persist with "H↦").
    - apply Qp.lt_sum in Hdq as (q2 & ->).
      iDestruct (fractional_split with "H↦") as "(H↦1 & H↦2)".
      iMod (mapsto_persist with "H↦2") as "H↦2".
      iDestruct (mapsto_combine with "H↦1 H↦2") as "($ & _)". done.
  Qed.
  Lemma chain_cons_spec t dq vs next v :
    ✓ dq →
    {{{ chain_model t dq vs next }}}
      chain_cons v t
    {{{ t', RET t'; chain_model t' dq (v :: vs) next }}}.
  Proof.
    iIntros "% %Φ Hmodel HΦ".
    iApply wp_fupd. wp_apply (record_two_make_spec with "[//]"). iIntros "%l' Hcell'".
    rewrite /record_two_model. iDestruct "Hcell'" as "(Hhd' & Htl')".
    iMod (mapsto_dfrac_relax with "Hhd'") as "Hhd'"; first done.
    iMod (mapsto_dfrac_relax with "Htl'") as "Htl'"; first done.
    iAssert (record_two_model l' dq v t) with "[Hhd' Htl']" as "Hcell'".
    { rewrite /record_two_model. iFrame. }
    iApply "HΦ". iExists l', t. auto with iFrame.
  Qed.

  Lemma chain_head_spec t dq v vs next :
    {{{ chain_model t dq (v :: vs) next }}}
      chain_head t
    {{{ RET v; chain_model t dq (v :: vs) next }}}.
  Proof.
    iIntros "%Φ (%l & %t' & -> & Hcell & Hmodel') HΦ".
    wp_rec. wp_pures.
    wp_apply (record_two_get0_spec with "Hcell"). iIntros "Hcell".
    iApply "HΦ". iExists l, t'. auto with iFrame.
  Qed.
  Lemma chain_tail_spec t dq v vs next :
    {{{ chain_model t dq (v :: vs) next }}}
      chain_tail t
    {{{ t', RET t'; chain_model t dq [v] t' ∗ chain_model t' dq vs next }}}.
  Proof.
    iIntros "%Φ (%l & %t' & -> & Hcell & Hmodel') HΦ".
    wp_rec. wp_pures.
    wp_apply (record_two_get1_spec with "Hcell"). iIntros "Hcell".
    iApply "HΦ". iFrame. iExists l, t'. auto with iFrame.
  Qed.

  Lemma chain_set_head_spec t v vs next w :
    {{{ chain_model t (DfracOwn 1) (v :: vs) next }}}
      chain_set_head t w
    {{{ RET #(); chain_model t (DfracOwn 1) (w :: vs) next }}}.
  Proof.
    iIntros "%Φ (%l & %t' & -> & Hcell & Hmodel') HΦ".
    wp_rec. wp_pures.
    wp_apply (record_two_set0_spec with "Hcell"). iIntros "Hcell".
    iApply "HΦ". iExists l, t'. auto with iFrame.
  Qed.
  Lemma chain_set_tail_spec t v vs next w :
    {{{ chain_model t (DfracOwn 1) (v :: vs) next }}}
      chain_set_tail t w
    {{{ t',
      RET #();
      chain_model t (DfracOwn 1) [v] w ∗
      chain_model t' (DfracOwn 1) vs next
    }}}.
  Proof.
    iIntros "%Φ (%l & %t' & -> & Hcell & Hmodel') HΦ".
    wp_rec. wp_pures.
    wp_apply (record_two_set1_spec with "Hcell"). iIntros "Hcell".
    iApply "HΦ". iFrame. iExists l, w. auto with iFrame.
  Qed.

  Lemma chain_advance_spec t dq vs next (i : Z) :
    (0 ≤ i ≤ length vs)%Z →
    {{{ chain_model t dq vs next }}}
      chain_advance t #i
    {{{ t',
      RET t';
      chain_model t dq (take (Z.to_nat i) vs) t' ∗
      chain_model t' dq (drop (Z.to_nat i) vs) next
    }}}.
  Proof.
    intros (Hi1 & Hi2). revert Hi2.
    rename i into _i. edestruct Z_of_nat_complete as (i & ->); first done. clear.
    rewrite -Nat2Z.inj_le Nat2Z.id.
    iInduction i as [| i] "IH" forall (t vs); iIntros "%Hi %Φ Hmodel HΦ"; wp_rec; wp_pures.
    - iApply "HΦ". auto with iFrame.
    - destruct vs as [| v vs]; simpl in Hi; first lia.
      wp_apply (chain_tail_spec with "Hmodel"). iIntros "%t' (Hmodel & Hmodel')".
      assert (S i - 1 = i)%Z as -> by lia.
      wp_apply ("IH" with "[] Hmodel'"); first (iPureIntro; lia). iIntros "%t'' (Hmodel' & Hmodel'')".
      iApply "HΦ". iFrame.
      iApply (chain_model_app_1 with "Hmodel Hmodel'").
  Qed.

  Lemma chain_get_spec t dq vs next (i : Z) v :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{ chain_model t dq vs next }}}
      chain_get t #i
    {{{ RET v; chain_model t dq vs next }}}.
  Proof.
    intros Hi. rename i into _i. edestruct Z_of_nat_complete as (i & ->); first done. clear.
    iIntros "%Hlookup %Φ Hmodel HΦ".
    rewrite Nat2Z.id in Hlookup. pose proof (lookup_lt_Some vs i v Hlookup).
    wp_rec. wp_pures.
    wp_apply (chain_advance_spec with "Hmodel"); first lia.
    iIntros "%t' (Hmodel & Hmodel')".
    rewrite Nat2Z.id.
    rewrite -(take_drop i vs) lookup_app_r in Hlookup; last (rewrite take_length; lia).
    rewrite take_length min_l in Hlookup; last lia.
    rewrite Nat.sub_diag in Hlookup.
    destruct (drop i vs) as [| _v vs'] eqn:Heq; first done. apply (inj Some) in Hlookup as ->.
    wp_apply (chain_head_spec with "Hmodel'"). iIntros "Hmodel'".
    iApply "HΦ".
    iEval (rewrite -(take_drop i vs) Heq). iApply (chain_model_app_1 with "Hmodel Hmodel'").
  Qed.
  Lemma chain_set_spec t vs next (i : Z) v w :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{ chain_model t (DfracOwn 1) vs next }}}
      chain_set t #i w
    {{{ RET #(); chain_model t (DfracOwn 1) (<[Z.to_nat i := w]> vs) next }}}.
  Proof.
    intros Hi. rename i into _i. edestruct Z_of_nat_complete as (i & ->); first done. clear.
    iIntros "%Hlookup %Φ Hmodel HΦ".
    rewrite Nat2Z.id in Hlookup. pose proof (lookup_lt_Some vs i v Hlookup).
    wp_rec. wp_pures.
    wp_apply (chain_advance_spec with "Hmodel"); first lia.
    iIntros "%t' (Hmodel & Hmodel')".
    rewrite Nat2Z.id.
    rewrite -(take_drop i vs) lookup_app_r in Hlookup; last (rewrite take_length; lia).
    rewrite take_length min_l in Hlookup; last lia.
    rewrite Nat.sub_diag in Hlookup.
    destruct (drop i vs) as [| _v vs'] eqn:Heq; first done. apply (inj Some) in Hlookup as ->.
    wp_apply (chain_set_head_spec with "Hmodel'"). iIntros "Hmodel'".
    iApply "HΦ".
    iEval (rewrite -(take_drop i vs) Heq).
    rewrite insert_app_r_alt; last (rewrite take_length; lia).
    rewrite take_length min_l; last lia.
    rewrite Nat.sub_diag.
    iApply (chain_model_app_1 with "Hmodel Hmodel'").
  Qed.
End heapGS.

#[global] Opaque chain_cons.
#[global] Opaque chain_head.
#[global] Opaque chain_tail.
#[global] Opaque chain_set_head.
#[global] Opaque chain_set_tail.
#[global] Opaque chain_advance.
#[global] Opaque chain_get.
#[global] Opaque chain_set.

#[global] Typeclasses Opaque chain_model.
