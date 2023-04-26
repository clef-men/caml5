From iris.proofmode Require Import
  proofmode.

From caml5 Require Import
  prelude.
From caml5 Require Export
  base.
From caml5.algebra Require Import
  lib.mono_states.

Section sts.
  Context `{Countable key}.
  Context `(step : relation state).

  Notation steps := (rtc step).

  Class StsCellsG Σ := {
    mono_states_G_inG : inG Σ (mono_states_UR key step) ;
  }.
  #[local] Existing Instance mono_states_G_inG.

  Definition mono_states_Σ := #[
    GFunctor (mono_states_UR key step)
  ].
  #[global] Instance subG_mono_states_Σ Σ :
    subG mono_states_Σ Σ →
    StsCellsG Σ.
  Proof.
    solve_inG.
  Qed.

  Section mono_states_G.
    Context `{mono_states_G : !StsCellsG Σ}.

    Definition mono_states_auth γ dq ss :=
      own γ (mono_states_auth step dq ss).
    Definition mono_states_mapsto γ k q s :=
      own γ (mono_states_mapsto step k q s).
    Definition mono_states_lb γ k s :=
      own γ (mono_states_lb step k s).

    #[global] Instance mono_states_auth_timeless γ dq ss :
      Timeless (mono_states_auth γ dq ss).
    Proof.
      apply _.
    Qed.
    #[global] Instance mono_states_auth_persistent γ ss :
      Persistent (mono_states_auth γ DfracDiscarded ss).
    Proof.
      apply _.
    Qed.
    #[global] Instance mono_states_mapsto_timeless γ k q s :
      Timeless (mono_states_mapsto γ k q s).
    Proof.
      apply _.
    Qed.
    #[global] Instance mono_states_lb_timeless γ k s :
      Timeless (mono_states_lb γ k s).
    Proof.
      apply _.
    Qed.
    #[global] Instance mono_states_lb_persistent γ k s :
      Persistent (mono_states_lb γ k s).
    Proof.
      apply _.
    Qed.

    #[global] Instance mono_states_auth_fractional γ ss :
      Fractional (λ q, mono_states_auth γ (DfracOwn q) ss).
    Proof.
      intros ?*. rewrite -own_op -mono_states_auth_dfrac_op //.
    Qed.
    #[global] Instance mono_states_auth_as_fractional γ q ss :
      AsFractional (mono_states_auth γ (DfracOwn q) ss) (λ q, mono_states_auth γ (DfracOwn q) ss) q.
    Proof.
      split; [done | apply _].
    Qed.
    #[global] Instance mono_states_mapsto_fractional γ k s :
      Fractional (λ q, mono_states_mapsto γ k q s).
    Proof.
      intros ?*. rewrite -own_op -mono_states_mapsto_frac_op //.
    Qed.
    #[global] Instance mono_states_mapsto_as_fractional γ k q s :
      AsFractional (mono_states_mapsto γ k q s) (λ q, mono_states_mapsto γ k q s) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma mono_states_alloc :
      ⊢ |==> ∃ γ,
        mono_states_auth γ (DfracOwn 1) ∅.
    Proof.
      apply own_alloc, mono_states_auth_valid.
    Qed.

    Lemma mono_states_auth_valid γ dq ss :
      mono_states_auth γ dq ss -∗
      ⌜✓ dq⌝.
    Proof.
      iIntros "Hauth".
      iDestruct (own_valid with "Hauth") as %?%mono_states_auth_dfrac_valid. done.
    Qed.
    Lemma mono_states_auth_combine `{!AntiSymm (=) steps} γ dq1 ss1 dq2 ss2 :
      mono_states_auth γ dq1 ss1 -∗
      mono_states_auth γ dq2 ss2 -∗
        mono_states_auth γ (dq1 ⋅ dq2) ss1 ∗
        ⌜ss1 = ss2⌝.
    Proof.
      iIntros "Hauth1 Hauth2". iCombine "Hauth1 Hauth2" as "Hauth".
      iDestruct (own_valid with "Hauth") as %(_ & ->)%mono_states_auth_dfrac_op_valid.
      rewrite -mono_states_auth_dfrac_op. naive_solver.
    Qed.
    Lemma mono_states_auth_valid_2 `{!AntiSymm (=) steps} γ dq1 ss1 dq2 ss2 :
      mono_states_auth γ dq1 ss1 -∗
      mono_states_auth γ dq2 ss2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ ss1 = ss2⌝.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (mono_states_auth_combine with "Hauth1 Hauth2") as "(Hauth & ->)".
      iDestruct (mono_states_auth_valid with "Hauth") as %?. done.
    Qed.
    Lemma mono_states_auth_agree `{!AntiSymm (=) steps} γ dq1 ss1 dq2 ss2 :
      mono_states_auth γ dq1 ss1 -∗
      mono_states_auth γ dq2 ss2 -∗
      ⌜ss1 = ss2⌝.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (mono_states_auth_valid_2 with "Hauth1 Hauth2") as "(_ & $)".
    Qed.
    Lemma mono_states_auth_exclusive `{!AntiSymm (=) steps} γ ss1 ss2 :
      mono_states_auth γ (DfracOwn 1) ss1 -∗
      mono_states_auth γ (DfracOwn 1) ss2 -∗
      False.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (mono_states_auth_valid_2 with "Hauth1 Hauth2") as "(% & _)". done.
    Qed.

    Lemma mono_states_mapsto_valid γ k q s :
      mono_states_mapsto γ k q s -∗
      ⌜✓ q⌝.
    Proof.
      iIntros "Hmapsto".
      iDestruct (own_valid with "Hmapsto") as %?%mono_states_mapsto_frac_valid. done.
    Qed.
    Lemma mono_states_mapsto_combine `{!AntiSymm (=) steps} γ k q1 s1 q2 s2 :
      mono_states_mapsto γ k q1 s1 -∗
      mono_states_mapsto γ k q2 s2 -∗
        mono_states_mapsto γ k (q1 ⋅ q2) s1 ∗
        ⌜s1 = s2⌝.
    Proof.
      iIntros "Hmapsto1 Hmapsto2". iCombine "Hmapsto1 Hmapsto2" as "Hmapsto".
      iDestruct (own_valid with "Hmapsto") as %(_ & ->)%mono_states_mapsto_frac_op_valid.
      rewrite -mono_states_mapsto_frac_op. naive_solver.
    Qed.
    Lemma mono_states_mapsto_valid_2 `{!AntiSymm (=) steps} γ k q1 s1 q2 s2 :
      mono_states_mapsto γ k q1 s1 -∗
      mono_states_mapsto γ k q2 s2 -∗
      ⌜✓ (q1 ⋅ q2) ∧ s1 = s2⌝.
    Proof.
      iIntros "Hmapsto1 Hmapsto2".
      iDestruct (mono_states_mapsto_combine with "Hmapsto1 Hmapsto2") as "(Hmapsto & ->)".
      iDestruct (mono_states_mapsto_valid with "Hmapsto") as %?. done.
    Qed.
    Lemma mono_states_mapsto_agree `{!AntiSymm (=) steps} γ k q1 s1 q2 s2 :
      mono_states_mapsto γ k q1 s1 -∗
      mono_states_mapsto γ k q2 s2 -∗
      ⌜s1 = s2⌝.
    Proof.
      iIntros "Hmapsto1 Hmapsto2".
      iDestruct (mono_states_mapsto_valid_2 with "Hmapsto1 Hmapsto2") as "(_ & $)".
    Qed.
    Lemma mono_states_mapsto_exclusive `{!AntiSymm (=) steps} γ k s1 s2 :
      mono_states_mapsto γ k 1 s1 -∗
      mono_states_mapsto γ k 1 s2 -∗
      False.
    Proof.
      iIntros "Hmapsto1 Hmapsto2".
      iDestruct (mono_states_mapsto_valid_2 with "Hmapsto1 Hmapsto2") as "(% & _)". done.
    Qed.

    Lemma mono_states_auth_mapsto_valid `{!AntiSymm (=) steps} γ dq ss k q s :
      mono_states_auth γ dq ss -∗
      mono_states_mapsto γ k q s -∗
      ⌜ss !! k = Some s⌝.
    Proof.
      iIntros "Hauth Hmapsto".
      iDestruct (own_valid_2 with "Hauth Hmapsto") as %?%mono_states_auth_mapsto_dfrac_valid.
      naive_solver.
    Qed.

    Lemma mono_states_auth_lb_valid γ dq ss k t :
      mono_states_auth γ dq ss -∗
      mono_states_lb γ k t -∗
      ⌜∃ s, ss !! k = Some s ∧ steps t s⌝.
    Proof.
      iIntros "Hauth Hlb".
      iDestruct (own_valid_2 with "Hauth Hlb") as %?%mono_states_auth_dfrac_lb_valid.
      naive_solver.
    Qed.

    Lemma mono_states_mapsto_lb_valid γ k q s t :
      mono_states_mapsto γ k q s -∗
      mono_states_lb γ k t -∗
      ⌜steps t s⌝.
    Proof.
      iIntros "Hmapsto Hlb".
      iDestruct (own_valid_2 with "Hmapsto Hlb") as %?%mono_states_mapsto_frac_lb_valid.
      naive_solver.
    Qed.

    Lemma mono_states_lb_get γ k q s :
      mono_states_mapsto γ k q s -∗
      mono_states_lb γ k s.
    Proof.
      apply own_mono, mono_states_lb_included.
    Qed.
    Lemma mono_states_lb_mono {γ k s} s' :
      steps s' s →
      mono_states_lb γ k s -∗
      mono_states_lb γ k s'.
    Proof.
      intros. apply own_mono, mono_states_lb_mono. done.
    Qed.

    Lemma mono_states_auth_persist γ dq ss :
      mono_states_auth γ dq ss ==∗
      mono_states_auth γ DfracDiscarded ss.
    Proof.
      iApply own_update. apply mono_states_auth_persist.
    Qed.
    Lemma mono_states_auth_alloc {γ ss} k s :
      ss !! k = None →
      mono_states_auth γ (DfracOwn 1) ss ==∗
      mono_states_auth γ (DfracOwn 1) (<[k := s]> ss).
    Proof.
      iIntros "% Hauth".
      iMod (own_update with "Hauth"); first apply mono_states_auth_alloc; done.
    Qed.

    Lemma mono_states_update `{!AntiSymm (=) steps} {γ ss k s} s' :
      steps s s' →
      mono_states_auth γ (DfracOwn 1) ss -∗
      mono_states_mapsto γ k 1 s ==∗
        mono_states_auth γ (DfracOwn 1) (<[k := s']> ss) ∗
        mono_states_mapsto γ k 1 s'.
    Proof.
      iIntros "% Hauth Hmapsto".
      iMod (own_update_2 with "Hauth Hmapsto") as "($ & $)"; first apply mono_states_update; done.
    Qed.
  End mono_states_G.
End sts.

#[global] Opaque mono_states_auth.
#[global] Opaque mono_states_mapsto.
#[global] Opaque mono_states_lb.
