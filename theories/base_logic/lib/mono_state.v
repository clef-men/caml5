From iris.proofmode Require Import
  proofmode.

From caml5 Require Import
  prelude.
From caml5 Require Export
  base.
From caml5.algebra Require Import
  lib.mono_state.

Section sts.
  Context `(step : relation state).

  Notation steps := (rtc step).

  Class StsCellG Σ := {
    mono_state_G_inG : inG Σ (mono_state_UR step) ;
  }.
  #[local] Existing Instance mono_state_G_inG.

  Definition mono_state_Σ := #[
    GFunctor (mono_state_UR step)
  ].
  #[global] Instance subG_mono_state_Σ Σ :
    subG mono_state_Σ Σ →
    StsCellG Σ.
  Proof.
    solve_inG.
  Qed.

  Section mono_state_G.
    Context `{mono_state_G : !StsCellG Σ}.

    Definition mono_state_auth γ dq s :=
      own γ (mono_state_auth step dq s).
    Definition mono_state_lb γ s :=
      own γ (mono_state_lb step s).

    #[global] Instance mono_state_auth_timeless γ dq s :
      Timeless (mono_state_auth γ dq s).
    Proof.
      apply _.
    Qed.
    #[global] Instance mono_state_auth_persistent γ s :
      Persistent (mono_state_auth γ DfracDiscarded s).
    Proof.
      apply _.
    Qed.
    #[global] Instance mono_state_lb_timeless γ s :
      Timeless (mono_state_lb γ s).
    Proof.
      apply _.
    Qed.
    #[global] Instance mono_state_lb_persistent γ s :
      Persistent (mono_state_lb γ s).
    Proof.
      apply _.
    Qed.

    #[global] Instance mono_state_auth_fractional γ s :
      Fractional (λ q, mono_state_auth γ (DfracOwn q) s).
    Proof.
      intros ?*. rewrite -own_op -mono_state_auth_dfrac_op //.
    Qed.
    #[global] Instance mono_state_auth_as_fractional γ q s :
      AsFractional (mono_state_auth γ (DfracOwn q) s) (λ q, mono_state_auth γ (DfracOwn q) s) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma mono_state_alloc s :
      ⊢ |==> ∃ γ,
        mono_state_auth γ (DfracOwn 1) s.
    Proof.
      apply own_alloc, mono_state_auth_valid.
    Qed.

    Lemma mono_state_auth_valid γ dq s :
      mono_state_auth γ dq s -∗
      ⌜✓ dq⌝.
    Proof.
      iIntros "Hauth".
      iDestruct (own_valid with "Hauth") as %?%mono_state_auth_dfrac_valid. done.
    Qed.
    Lemma mono_state_auth_combine `{!AntiSymm (=) steps} γ dq1 s1 dq2 s2 :
      mono_state_auth γ dq1 s1 -∗
      mono_state_auth γ dq2 s2 -∗
        mono_state_auth γ (dq1 ⋅ dq2) s1 ∗
        ⌜s1 = s2⌝.
    Proof.
      iIntros "Hauth1 Hauth2". iCombine "Hauth1 Hauth2" as "Hauth".
      iDestruct (own_valid with "Hauth") as %(_ & ->)%mono_state_auth_dfrac_op_valid.
      rewrite -mono_state_auth_dfrac_op. naive_solver.
    Qed.
    Lemma mono_state_auth_valid_2 `{!AntiSymm (=) steps} γ dq1 s1 dq2 s2 :
      mono_state_auth γ dq1 s1 -∗
      mono_state_auth γ dq2 s2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ s1 = s2⌝.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (mono_state_auth_combine with "Hauth1 Hauth2") as "(Hauth & ->)".
      iDestruct (mono_state_auth_valid with "Hauth") as %?. done.
    Qed.
    Lemma mono_state_auth_agree `{!AntiSymm (=) steps} γ dq1 s1 dq2 s2 :
      mono_state_auth γ dq1 s1 -∗
      mono_state_auth γ dq2 s2 -∗
      ⌜s1 = s2⌝.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (mono_state_auth_valid_2 with "Hauth1 Hauth2") as "(_ & $)".
    Qed.
    Lemma mono_state_auth_dfrac_ne `{!AntiSymm (=) steps} γ1 dq1 s1 γ2 dq2 s2 :
      ¬ ✓ (dq1 ⋅ dq2) →
      mono_state_auth γ1 dq1 s1 -∗
      mono_state_auth γ2 dq2 s2 -∗
      ⌜γ1 ≠ γ2⌝.
    Proof.
      iIntros "% Hauth1 Hauth2" (->).
      iDestruct (mono_state_auth_valid_2 with "Hauth1 Hauth2") as %?; naive_solver.
    Qed.
    Lemma mono_state_auth_ne `{!AntiSymm (=) steps} γ1 s1 γ2 dq2 s2 :
      mono_state_auth γ1 (DfracOwn 1) s1 -∗
      mono_state_auth γ2 dq2 s2 -∗
      ⌜γ1 ≠ γ2⌝.
    Proof.
      intros. iApply mono_state_auth_dfrac_ne; [done.. | intros []%(exclusive_l _)].
    Qed.
    Lemma mono_state_auth_exclusive `{!AntiSymm (=) steps} γ s1 s2 :
      mono_state_auth γ (DfracOwn 1) s1 -∗
      mono_state_auth γ (DfracOwn 1) s2 -∗
      False.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (mono_state_auth_valid_2 with "Hauth1 Hauth2") as "(% & _)". done.
    Qed.
    Lemma mono_state_auth_persist γ dq s :
      mono_state_auth γ dq s ==∗
      mono_state_auth γ DfracDiscarded s.
    Proof.
      iApply own_update. apply mono_state_auth_persist.
    Qed.

    Lemma mono_state_lb_get γ q s :
      mono_state_auth γ q s -∗
      mono_state_lb γ s.
    Proof.
      apply own_mono, mono_state_lb_included'.
    Qed.
    Lemma mono_state_lb_mono {γ s} s' :
      steps s' s →
      mono_state_lb γ s -∗
      mono_state_lb γ s'.
    Proof.
      intros. apply own_mono, mono_state_lb_mono. done.
    Qed.

    Lemma mono_state_valid γ dq s t :
      mono_state_auth γ dq s -∗
      mono_state_lb γ t -∗
      ⌜steps t s⌝.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (own_valid_2 with "Hauth1 Hauth2") as %?%mono_state_both_dfrac_valid.
      naive_solver.
    Qed.

    Lemma mono_state_update {γ s} s' :
      steps s s' →
      mono_state_auth γ (DfracOwn 1) s ==∗
      mono_state_auth γ (DfracOwn 1) s'.
    Proof.
      iIntros "% Hauth".
      iMod (own_update with "Hauth"); first apply mono_state_auth_update; done.
    Qed.
  End mono_state_G.
End sts.

#[global] Opaque mono_state_auth.
#[global] Opaque mono_state_lb.
