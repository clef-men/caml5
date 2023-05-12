From iris.bi Require Import
  interface.
From iris.bi Require Export
  big_op.
From iris.proofmode Require Import
  proofmode.

From caml5 Require Import
  prelude.

Section big_sepL.
  Context {PROP : bi}.

  Lemma big_sepL_mono_strong `{!BiAffine PROP} {A1 A2} (l1 : list A1) (l2 : list A2) Φ1 Φ2 :
    length l1 = length l2 →
    ⊢@{PROP}
      ( [∗ list] i ∈ seq 0 (length l1), ∀ x1 x2,
          ⌜l1 !! i = Some x1 ∧ l2 !! i = Some x2⌝ -∗
          Φ1 i x1 -∗
          Φ2 i x2
      ) -∗
      ([∗ list] i ↦ x ∈ l1, Φ1 i x) -∗
      ([∗ list] i ↦ x ∈ l2, Φ2 i x).
  Proof.
    iIntros "%Hl2 HΦ HΦ1". remember (length l1) as sz eqn:Hl1.
    iInduction sz as [| sz] "IH" forall (l1 l2 Hl1 Hl2).
    { apply symmetry, nil_length_inv in Hl2 as ->. done. }
    revert dependent l1. refine (rev_ind _ _ _); [| intros x1 l1 _]; intros Hl1; first done.
    revert dependent l2. refine (rev_ind _ _ _); [| intros x2 l2 _]; intros Hl2; first done.
    rewrite !app_length !Nat.add_1_r !Nat.succ_inj_wd in Hl1 Hl2.
    rewrite List.seq_S /=. iDestruct (big_sepL_snoc with "HΦ") as "(HΦ & HΦ')".
    iDestruct (big_sepL_snoc with "HΦ1") as "(HΦ1 & HΦ1')".
    iApply big_sepL_snoc. iSplitL "HΦ HΦ1".
    - iApply ("IH" with "[] [] [HΦ] HΦ1"); try done.
      iApply (big_sepL_mono with "HΦ"). iIntros "%i %_i %H_i HΦ %x1' %x2' % HΦ1". apply lookup_seq in H_i as (-> & ?).
      iApply "HΦ"; naive_solver eauto using lookup_app_l_Some.
    - rewrite -Hl1 -Hl2. iApply ("HΦ'" with "[] HΦ1'"). rewrite !list_lookup_middle //.
  Qed.
  Lemma big_sepL_mono_strong' `{!BiAffine PROP} {A1 A2} (l1 : list A1) (l2 : list A2) Φ1 Φ2 :
    length l1 = length l2 →
    ⊢@{PROP}
      □ (
        ∀ i x1 x2,
        ⌜l1 !! i = Some x1 ∧ l2 !! i = Some x2⌝ -∗
        Φ1 i x1 -∗
        Φ2 i x2
      ) -∗
      ([∗ list] i ↦ x ∈ l1, Φ1 i x) -∗
      ([∗ list] i ↦ x ∈ l2, Φ2 i x).
  Proof.
    iIntros "% #HΦ HΦ1".
    iApply (big_sepL_mono_strong with "[HΦ] HΦ1"); first done.
    iApply big_sepL_intro. iIntros "!> %i %_i % %x1 %x2 % HΨ".
    iApply ("HΦ" with "[//] HΨ").
  Qed.

  Lemma big_sepL_seq_index `{!BiAffine PROP} {A} (l : list A) sz Φ :
    length l = sz →
    ([∗ list] i ∈ seq 0 sz, Φ i) ⊣⊢@{PROP}
    [∗ list] i ↦ _ ∈ l, Φ i.
  Proof.
    intros. iSplit.
    all: iIntros "H".
    all: iApply (big_sepL_mono_strong' with "[] H"); first rewrite seq_length //.
    all: iIntros "!> %i %_i % %".
    all: pose proof lookup_seq.
    all: naive_solver.
  Qed.
  Lemma big_sepL_seq_index_1 `{!BiAffine PROP} {A} (l : list A) sz Φ :
    length l = sz →
    ⊢@{PROP}
      ([∗ list] i ∈ seq 0 sz, Φ i) -∗
      [∗ list] i ↦ _ ∈ l, Φ i.
  Proof.
    intros. rewrite big_sepL_seq_index; last eauto. naive_solver.
  Qed.
  Lemma big_sepL_seq_index_2 `{!BiAffine PROP} {A} (l : list A) sz Φ :
    length l = sz →
    ⊢@{PROP}
      ([∗ list] i ↦ _ ∈ l, Φ i) -∗
      [∗ list] i ∈ seq 0 sz, Φ i.
  Proof.
    intros. rewrite big_sepL_seq_index; last eauto. naive_solver.
  Qed.

  Lemma big_sepL_seq_shift `{!BiAffine PROP} j i sz Φ :
    ([∗ list] k ∈ seq i sz, Φ k) ⊣⊢@{PROP}
    [∗ list] k ∈ seq (i + j) sz, Φ (k - j).
  Proof.
    iSplit.
    all: iApply big_sepL_mono_strong'; first rewrite !seq_length //.
    all: iIntros "!>" (k ? ? ((-> & _)%lookup_seq & (-> & _)%lookup_seq)).
    all: assert (i + j + k - j = i + k) as -> by lia.
    all: auto.
  Qed.
  Lemma big_sepL_seq_shift_1 `{!BiAffine PROP} j i sz Φ :
    ⊢@{PROP}
      ([∗ list] k ∈ seq i sz, Φ k) -∗
      [∗ list] k ∈ seq (i + j) sz, Φ (k - j).
  Proof.
    rewrite big_sepL_seq_shift. naive_solver.
  Qed.
  Lemma big_sepL_seq_shift_2 `{!BiAffine PROP} j i sz Φ :
    ⊢@{PROP}
      ([∗ list] k ∈ seq (i + j) sz, Φ (k - j)) -∗
      [∗ list] k ∈ seq i sz, Φ k.
  Proof.
    rewrite -big_sepL_seq_shift. naive_solver.
  Qed.
End big_sepL.
