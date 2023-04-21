From iris.proofmode Require Import
  proofmode.

From caml5 Require Import
  prelude.
From caml5 Require Export
  base.
From caml5.algebra Require Import
  lib.sts_cell.

Section sts.
  Context `(step : relation state).

  Notation steps := (rtc step).

  Class StsCellG Σ := {
    sts_cell_G_inG : inG Σ (sts_cell_UR step) ;
  }.
  #[local] Existing Instance sts_cell_G_inG.

  Definition sts_cell_Σ := #[
    GFunctor (sts_cell_UR step)
  ].
  #[global] Instance subG_sts_cell_Σ Σ :
    subG sts_cell_Σ Σ →
    StsCellG Σ.
  Proof.
    solve_inG.
  Qed.

  Section sts_cell_G.
    Context `{sts_cell_G : !StsCellG Σ}.

    Definition sts_cell_auth γ dq s :=
      own γ (sts_cell_auth step dq s).
    Definition sts_cell_lb γ s :=
      own γ (sts_cell_lb step s).

    #[global] Instance sts_cell_auth_timeless γ dq s :
      Timeless (sts_cell_auth γ dq s).
    Proof.
      apply _.
    Qed.
    #[global] Instance sts_cell_auth_persistent γ s :
      Persistent (sts_cell_auth γ DfracDiscarded s).
    Proof.
      apply _.
    Qed.
    #[global] Instance sts_cell_lb_timeless γ s :
      Timeless (sts_cell_lb γ s).
    Proof.
      apply _.
    Qed.
    #[global] Instance sts_cell_lb_persistent γ s :
      Persistent (sts_cell_lb γ s).
    Proof.
      apply _.
    Qed.

    #[global] Instance sts_cell_auth_fractional γ s :
      Fractional (λ q, sts_cell_auth γ (DfracOwn q) s).
    Proof.
      intros ?*. rewrite -own_op -sts_cell_auth_dfrac_op //.
    Qed.
    #[global] Instance sts_cell_auth_as_fractional γ q s :
      AsFractional (sts_cell_auth γ (DfracOwn q) s) (λ q, sts_cell_auth γ (DfracOwn q) s) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma sts_cell_alloc s :
      ⊢ |==> ∃ γ,
        sts_cell_auth γ (DfracOwn 1) s.
    Proof.
      apply own_alloc, sts_cell_auth_valid.
    Qed.

    Lemma sts_cell_auth_valid γ dq s :
      sts_cell_auth γ dq s -∗
      ⌜✓ dq⌝.
    Proof.
      iIntros "Hauth".
      iDestruct (own_valid with "Hauth") as %?%sts_cell_auth_dfrac_valid. done.
    Qed.
    Lemma sts_cell_auth_combine `{!AntiSymm (=) steps} γ dq1 s1 dq2 s2 :
      sts_cell_auth γ dq1 s1 -∗
      sts_cell_auth γ dq2 s2 -∗
        sts_cell_auth γ (dq1 ⋅ dq2) s1 ∗
        ⌜s1 = s2⌝.
    Proof.
      iIntros "Hauth1 Hauth2". iCombine "Hauth1 Hauth2" as "Hauth".
      iDestruct (own_valid with "Hauth") as %(_ & ->)%sts_cell_auth_dfrac_op_valid.
      rewrite -sts_cell_auth_dfrac_op. naive_solver.
    Qed.
    Lemma sts_cell_auth_valid_2 `{!AntiSymm (=) steps} γ dq1 s1 dq2 s2 :
      sts_cell_auth γ dq1 s1 -∗
      sts_cell_auth γ dq2 s2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ s1 = s2⌝.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (sts_cell_auth_combine with "Hauth1 Hauth2") as "(Hauth & ->)".
      iDestruct (sts_cell_auth_valid with "Hauth") as %?. done.
    Qed.
    Lemma sts_cell_auth_agree `{!AntiSymm (=) steps} γ dq1 s1 dq2 s2 :
      sts_cell_auth γ dq1 s1 -∗
      sts_cell_auth γ dq2 s2 -∗
      ⌜s1 = s2⌝.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (sts_cell_auth_valid_2 with "Hauth1 Hauth2") as "(_ & $)".
    Qed.
    Lemma sts_cell_auth_exclusive `{!AntiSymm (=) steps} γ s1 s2 :
      sts_cell_auth γ (DfracOwn 1) s1 -∗
      sts_cell_auth γ (DfracOwn 1) s2 -∗
      False.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (sts_cell_auth_valid_2 with "Hauth1 Hauth2") as "(% & _)". done.
    Qed.

    Lemma sts_cell_lb_get γ q s :
      sts_cell_auth γ q s -∗
      sts_cell_lb γ s.
    Proof.
      apply own_mono, sts_cell_lb_included'.
    Qed.
    Lemma sts_cell_lb_mono {γ s} s' :
      steps s' s →
      sts_cell_lb γ s -∗
      sts_cell_lb γ s'.
    Proof.
      intros. apply own_mono, sts_cell_lb_mono. done.
    Qed.

    Lemma sts_cell_valid γ dq s t :
      sts_cell_auth γ dq s -∗
      sts_cell_lb γ t -∗
      ⌜steps t s⌝.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (own_valid_2 with "Hauth1 Hauth2") as %?%sts_cell_both_dfrac_valid.
      naive_solver.
    Qed.

    Lemma sts_cell_auth_persist γ dq s :
      sts_cell_auth γ dq s ==∗
      sts_cell_auth γ DfracDiscarded s.
    Proof.
      iApply own_update. apply sts_cell_auth_persist.
    Qed.

    Lemma sts_cell_update {γ s} s' :
      steps s s' →
      sts_cell_auth γ (DfracOwn 1) s ==∗
      sts_cell_auth γ (DfracOwn 1) s'.
    Proof.
      iIntros "% Hauth".
      iMod (own_update with "Hauth"); first apply sts_cell_auth_update; done.
    Qed.
  End sts_cell_G.
End sts.

#[global] Opaque sts_cell_auth.
#[global] Opaque sts_cell_lb.
