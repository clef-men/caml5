From iris.proofmode Require Import
  proofmode.

From caml5 Require Import
  prelude.
From caml5 Require Export
  base.
From caml5.algebra Require Import
  lib.sts_cells.

Section sts.
  Context `{Countable key}.
  Context `(step : relation state).

  Notation steps := (rtc step).

  Class StsCellsG Σ := {
    sts_cells_G_inG : inG Σ (sts_cells_UR key step) ;
  }.
  #[local] Existing Instance sts_cells_G_inG.

  Definition sts_cells_Σ := #[
    GFunctor (sts_cells_UR key step)
  ].
  #[global] Instance subG_sts_cells_Σ Σ :
    subG sts_cells_Σ Σ →
    StsCellsG Σ.
  Proof.
    solve_inG.
  Qed.

  Section sts_cells_G.
    Context `{sts_cells_G : !StsCellsG Σ}.

    Definition sts_cells_auth γ dq ss :=
      own γ (sts_cells_auth step dq ss).
    Definition sts_cells_mapsto γ k q s :=
      own γ (sts_cells_mapsto step k q s).
    Definition sts_cells_lb γ k s :=
      own γ (sts_cells_lb step k s).

    #[global] Instance sts_cells_auth_timeless γ dq ss :
      Timeless (sts_cells_auth γ dq ss).
    Proof.
      apply _.
    Qed.
    #[global] Instance sts_cells_auth_persistent γ ss :
      Persistent (sts_cells_auth γ DfracDiscarded ss).
    Proof.
      apply _.
    Qed.
    #[global] Instance sts_cells_mapsto_timeless γ k q s :
      Timeless (sts_cells_mapsto γ k q s).
    Proof.
      apply _.
    Qed.
    #[global] Instance sts_cells_lb_timeless γ k s :
      Timeless (sts_cells_lb γ k s).
    Proof.
      apply _.
    Qed.
    #[global] Instance sts_cells_lb_persistent γ k s :
      Persistent (sts_cells_lb γ k s).
    Proof.
      apply _.
    Qed.

    #[global] Instance sts_cells_auth_fractional γ ss :
      Fractional (λ q, sts_cells_auth γ (DfracOwn q) ss).
    Proof.
      intros ?*. rewrite -own_op -sts_cells_auth_dfrac_op //.
    Qed.
    #[global] Instance sts_cells_auth_as_fractional γ q ss :
      AsFractional (sts_cells_auth γ (DfracOwn q) ss) (λ q, sts_cells_auth γ (DfracOwn q) ss) q.
    Proof.
      split; [done | apply _].
    Qed.
    #[global] Instance sts_cells_mapsto_fractional γ k s :
      Fractional (λ q, sts_cells_mapsto γ k q s).
    Proof.
      intros ?*. rewrite -own_op -sts_cells_mapsto_frac_op //.
    Qed.
    #[global] Instance sts_cells_mapsto_as_fractional γ k q s :
      AsFractional (sts_cells_mapsto γ k q s) (λ q, sts_cells_mapsto γ k q s) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma sts_cells_alloc :
      ⊢ |==> ∃ γ,
        sts_cells_auth γ (DfracOwn 1) ∅.
    Proof.
      apply own_alloc, sts_cells_auth_valid.
    Qed.

    Lemma sts_cells_auth_valid γ dq ss :
      sts_cells_auth γ dq ss -∗
      ⌜✓ dq⌝.
    Proof.
      iIntros "Hauth".
      iDestruct (own_valid with "Hauth") as %?%sts_cells_auth_dfrac_valid. done.
    Qed.
    Lemma sts_cells_auth_combine `{!AntiSymm (=) steps} γ dq1 ss1 dq2 ss2 :
      sts_cells_auth γ dq1 ss1 -∗
      sts_cells_auth γ dq2 ss2 -∗
        sts_cells_auth γ (dq1 ⋅ dq2) ss1 ∗
        ⌜ss1 = ss2⌝.
    Proof.
      iIntros "Hauth1 Hauth2". iCombine "Hauth1 Hauth2" as "Hauth".
      iDestruct (own_valid with "Hauth") as %(_ & ->)%sts_cells_auth_dfrac_op_valid.
      rewrite -sts_cells_auth_dfrac_op. naive_solver.
    Qed.
    Lemma sts_cells_auth_valid_2 `{!AntiSymm (=) steps} γ dq1 ss1 dq2 ss2 :
      sts_cells_auth γ dq1 ss1 -∗
      sts_cells_auth γ dq2 ss2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ ss1 = ss2⌝.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (sts_cells_auth_combine with "Hauth1 Hauth2") as "(Hauth & ->)".
      iDestruct (sts_cells_auth_valid with "Hauth") as %?. done.
    Qed.
    Lemma sts_cells_auth_agree `{!AntiSymm (=) steps} γ dq1 ss1 dq2 ss2 :
      sts_cells_auth γ dq1 ss1 -∗
      sts_cells_auth γ dq2 ss2 -∗
      ⌜ss1 = ss2⌝.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (sts_cells_auth_valid_2 with "Hauth1 Hauth2") as "(_ & $)".
    Qed.
    Lemma sts_cells_auth_exclusive `{!AntiSymm (=) steps} γ ss1 ss2 :
      sts_cells_auth γ (DfracOwn 1) ss1 -∗
      sts_cells_auth γ (DfracOwn 1) ss2 -∗
      False.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (sts_cells_auth_valid_2 with "Hauth1 Hauth2") as "(% & _)". done.
    Qed.

    Lemma sts_cells_mapsto_valid γ k q s :
      sts_cells_mapsto γ k q s -∗
      ⌜✓ q⌝.
    Proof.
      iIntros "Hmapsto".
      iDestruct (own_valid with "Hmapsto") as %?%sts_cells_mapsto_frac_valid. done.
    Qed.
    Lemma sts_cells_mapsto_combine `{!AntiSymm (=) steps} γ k q1 s1 q2 s2 :
      sts_cells_mapsto γ k q1 s1 -∗
      sts_cells_mapsto γ k q2 s2 -∗
        sts_cells_mapsto γ k (q1 ⋅ q2) s1 ∗
        ⌜s1 = s2⌝.
    Proof.
      iIntros "Hmapsto1 Hmapsto2". iCombine "Hmapsto1 Hmapsto2" as "Hmapsto".
      iDestruct (own_valid with "Hmapsto") as %(_ & ->)%sts_cells_mapsto_frac_op_valid.
      rewrite -sts_cells_mapsto_frac_op. naive_solver.
    Qed.
    Lemma sts_cells_mapsto_valid_2 `{!AntiSymm (=) steps} γ k q1 s1 q2 s2 :
      sts_cells_mapsto γ k q1 s1 -∗
      sts_cells_mapsto γ k q2 s2 -∗
      ⌜✓ (q1 ⋅ q2) ∧ s1 = s2⌝.
    Proof.
      iIntros "Hmapsto1 Hmapsto2".
      iDestruct (sts_cells_mapsto_combine with "Hmapsto1 Hmapsto2") as "(Hmapsto & ->)".
      iDestruct (sts_cells_mapsto_valid with "Hmapsto") as %?. done.
    Qed.
    Lemma sts_cells_mapsto_agree `{!AntiSymm (=) steps} γ k q1 s1 q2 s2 :
      sts_cells_mapsto γ k q1 s1 -∗
      sts_cells_mapsto γ k q2 s2 -∗
      ⌜s1 = s2⌝.
    Proof.
      iIntros "Hmapsto1 Hmapsto2".
      iDestruct (sts_cells_mapsto_valid_2 with "Hmapsto1 Hmapsto2") as "(_ & $)".
    Qed.
    Lemma sts_cells_mapsto_exclusive `{!AntiSymm (=) steps} γ k s1 s2 :
      sts_cells_mapsto γ k 1 s1 -∗
      sts_cells_mapsto γ k 1 s2 -∗
      False.
    Proof.
      iIntros "Hmapsto1 Hmapsto2".
      iDestruct (sts_cells_mapsto_valid_2 with "Hmapsto1 Hmapsto2") as "(% & _)". done.
    Qed.

    Lemma sts_cells_auth_mapsto_valid `{!AntiSymm (=) steps} γ dq ss k q s :
      sts_cells_auth γ dq ss -∗
      sts_cells_mapsto γ k q s -∗
      ⌜ss !! k = Some s⌝.
    Proof.
      iIntros "Hauth Hmapsto".
      iDestruct (own_valid_2 with "Hauth Hmapsto") as %?%sts_cells_auth_mapsto_dfrac_valid.
      naive_solver.
    Qed.

    Lemma sts_cells_auth_lb_valid γ dq ss k t :
      sts_cells_auth γ dq ss -∗
      sts_cells_lb γ k t -∗
      ⌜∃ s, steps t s ∧ ss !! k = Some s⌝.
    Proof.
      iIntros "Hauth Hlb".
      iDestruct (own_valid_2 with "Hauth Hlb") as %?%sts_cells_auth_dfrac_lb_valid.
      naive_solver.
    Qed.

    Lemma sts_cells_mapsto_lb_valid γ k q s t :
      sts_cells_mapsto γ k q s -∗
      sts_cells_lb γ k t -∗
      ⌜steps t s⌝.
    Proof.
      iIntros "Hmapsto Hlb".
      iDestruct (own_valid_2 with "Hmapsto Hlb") as %?%sts_cells_mapsto_frac_lb_valid.
      naive_solver.
    Qed.

    Lemma sts_cells_lb_get γ k q s :
      sts_cells_mapsto γ k q s -∗
      sts_cells_lb γ k s.
    Proof.
      apply own_mono, sts_cells_lb_included.
    Qed.
    Lemma sts_cells_lb_mono {γ k s} s' :
      steps s' s →
      sts_cells_lb γ k s -∗
      sts_cells_lb γ k s'.
    Proof.
      intros. apply own_mono, sts_cells_lb_mono. done.
    Qed.

    Lemma sts_cells_auth_persist γ dq ss :
      sts_cells_auth γ dq ss ==∗
      sts_cells_auth γ DfracDiscarded ss.
    Proof.
      iApply own_update. apply sts_cells_auth_persist.
    Qed.
    Lemma sts_cells_auth_alloc {γ ss} k s :
      ss !! k = None →
      sts_cells_auth γ (DfracOwn 1) ss ==∗
      sts_cells_auth γ (DfracOwn 1) (<[k := s]> ss).
    Proof.
      iIntros "% Hauth".
      iMod (own_update with "Hauth"); first apply sts_cells_auth_alloc; done.
    Qed.

    Lemma sts_cells_update `{!AntiSymm (=) steps} {γ ss k s} s' :
      steps s s' →
      sts_cells_auth γ (DfracOwn 1) ss -∗
      sts_cells_mapsto γ k 1 s ==∗
        sts_cells_auth γ (DfracOwn 1) (<[k := s']> ss) ∗
        sts_cells_mapsto γ k 1 s'.
    Proof.
      iIntros "% Hauth Hmapsto".
      iMod (own_update_2 with "Hauth Hmapsto") as "($ & $)"; first apply sts_cells_update; done.
    Qed.
  End sts_cells_G.
End sts.

#[global] Opaque sts_cells_auth.
#[global] Opaque sts_cells_mapsto.
#[global] Opaque sts_cells_lb.
