From iris.proofmode Require Import
  proofmode.

From caml5 Require Import
  prelude.
From caml5 Require Export
  base.
From caml5.algebra Require Import
  lib.ribbon.

Section sts.
  Context `(step : relation state).

  Notation steps := (rtc step).

  Class RibbonG Σ := {
    ribbon_G_inG : inG Σ (ribbon_UR step) ;
  }.
  #[local] Existing Instance ribbon_G_inG.

  Definition ribbon_Σ := #[
    GFunctor (ribbon_UR step)
  ].
  #[global] Instance subG_ribbon_Σ Σ :
    subG ribbon_Σ Σ →
    RibbonG Σ.
  Proof.
    solve_inG.
  Qed.

  Section ribbon_G.
    Context `{ribbon_G : !RibbonG Σ}.

    Definition ribbon_auth γ dq rib :=
      own γ (ribbon_auth step dq rib).
    Definition ribbon_mapsto γ i q s :=
      own γ (ribbon_mapsto step i q s).
    Definition ribbon_lb γ i s :=
      own γ (ribbon_lb step i s).

    #[global] Instance ribbon_auth_timeless γ dq rib :
      Timeless (ribbon_auth γ dq rib).
    Proof.
      apply _.
    Qed.
    #[global] Instance ribbon_auth_persistent γ rib :
      Persistent (ribbon_auth γ DfracDiscarded rib).
    Proof.
      apply _.
    Qed.
    #[global] Instance ribbon_mapsto_timeless γ i q s :
      Timeless (ribbon_mapsto γ i q s).
    Proof.
      apply _.
    Qed.
    #[global] Instance ribbon_lb_timeless γ i s :
      Timeless (ribbon_lb γ i s).
    Proof.
      apply _.
    Qed.
    #[global] Instance ribbon_lb_persistent γ i s :
      Persistent (ribbon_lb γ i s).
    Proof.
      apply _.
    Qed.

    #[global] Instance ribbon_auth_fractional γ rib :
      Fractional (λ q, ribbon_auth γ (DfracOwn q) rib).
    Proof.
      intros ?*. rewrite -own_op -ribbon_auth_dfrac_op //.
    Qed.
    #[global] Instance ribbon_auth_as_fractional γ q rib :
      AsFractional (ribbon_auth γ (DfracOwn q) rib) (λ q, ribbon_auth γ (DfracOwn q) rib) q.
    Proof.
      split; [done | apply _].
    Qed.
    #[global] Instance ribbon_mapsto_fractional γ i s :
      Fractional (λ q, ribbon_mapsto γ i q s).
    Proof.
      intros ?*. rewrite -own_op -ribbon_mapsto_frac_op //.
    Qed.
    #[global] Instance ribbon_mapsto_as_fractional γ i q s :
      AsFractional (ribbon_mapsto γ i q s) (λ q, ribbon_mapsto γ i q s) q.
    Proof.
      split; [done | apply _].
    Qed.

    Lemma ribbon_alloc :
      ⊢ |==> ∃ γ,
        ribbon_auth γ (DfracOwn 1) [].
    Proof.
      apply own_alloc, ribbon_auth_valid.
    Qed.

    Lemma ribbon_auth_valid γ dq rib :
      ribbon_auth γ dq rib -∗
      ⌜✓ dq⌝.
    Proof.
      iIntros "Hauth".
      iDestruct (own_valid with "Hauth") as %?%ribbon_auth_dfrac_valid. done.
    Qed.
    Lemma ribbon_auth_combine `{!AntiSymm (=) steps} γ dq1 rib1 dq2 rib2 :
      ribbon_auth γ dq1 rib1 -∗
      ribbon_auth γ dq2 rib2 -∗
        ribbon_auth γ (dq1 ⋅ dq2) rib1 ∗
        ⌜rib1 = rib2⌝.
    Proof.
      iIntros "Hauth1 Hauth2". iCombine "Hauth1 Hauth2" as "Hauth".
      iDestruct (own_valid with "Hauth") as %(_ & ->)%ribbon_auth_dfrac_op_valid.
      rewrite -ribbon_auth_dfrac_op. naive_solver.
    Qed.
    Lemma ribbon_auth_valid_2 `{!AntiSymm (=) steps} γ dq1 rib1 dq2 rib2 :
      ribbon_auth γ dq1 rib1 -∗
      ribbon_auth γ dq2 rib2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ rib1 = rib2⌝.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (ribbon_auth_combine with "Hauth1 Hauth2") as "(Hauth & ->)".
      iDestruct (ribbon_auth_valid with "Hauth") as %?. done.
    Qed.
    Lemma ribbon_auth_agree `{!AntiSymm (=) steps} γ dq1 rib1 dq2 rib2 :
      ribbon_auth γ dq1 rib1 -∗
      ribbon_auth γ dq2 rib2 -∗
      ⌜rib1 = rib2⌝.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (ribbon_auth_valid_2 with "Hauth1 Hauth2") as "(_ & $)".
    Qed.
    Lemma ribbon_auth_exclusive `{!AntiSymm (=) steps} γ rib1 rib2 :
      ribbon_auth γ (DfracOwn 1) rib1 -∗
      ribbon_auth γ (DfracOwn 1) rib2 -∗
      False.
    Proof.
      iIntros "Hauth1 Hauth2".
      iDestruct (ribbon_auth_valid_2 with "Hauth1 Hauth2") as "(% & _)". done.
    Qed.

    Lemma ribbon_mapsto_valid γ i q s :
      ribbon_mapsto γ i q s -∗
      ⌜✓ q⌝.
    Proof.
      iIntros "Hmapsto".
      iDestruct (own_valid with "Hmapsto") as %?%ribbon_mapsto_frac_valid. done.
    Qed.
    Lemma ribbon_mapsto_combine `{!AntiSymm (=) steps} γ i q1 s1 q2 s2 :
      ribbon_mapsto γ i q1 s1 -∗
      ribbon_mapsto γ i q2 s2 -∗
        ribbon_mapsto γ i (q1 ⋅ q2) s1 ∗
        ⌜s1 = s2⌝.
    Proof.
      iIntros "Hmapsto1 Hmapsto2". iCombine "Hmapsto1 Hmapsto2" as "Hmapsto".
      iDestruct (own_valid with "Hmapsto") as %(_ & ->)%ribbon_mapsto_frac_op_valid.
      rewrite -ribbon_mapsto_frac_op. naive_solver.
    Qed.
    Lemma ribbon_mapsto_valid_2 `{!AntiSymm (=) steps} γ i q1 s1 q2 s2 :
      ribbon_mapsto γ i q1 s1 -∗
      ribbon_mapsto γ i q2 s2 -∗
      ⌜✓ (q1 ⋅ q2) ∧ s1 = s2⌝.
    Proof.
      iIntros "Hmapsto1 Hmapsto2".
      iDestruct (ribbon_mapsto_combine with "Hmapsto1 Hmapsto2") as "(Hmapsto & ->)".
      iDestruct (ribbon_mapsto_valid with "Hmapsto") as %?. done.
    Qed.
    Lemma ribbon_mapsto_agree `{!AntiSymm (=) steps} γ i q1 s1 q2 s2 :
      ribbon_mapsto γ i q1 s1 -∗
      ribbon_mapsto γ i q2 s2 -∗
      ⌜s1 = s2⌝.
    Proof.
      iIntros "Hmapsto1 Hmapsto2".
      iDestruct (ribbon_mapsto_valid_2 with "Hmapsto1 Hmapsto2") as "(_ & $)".
    Qed.
    Lemma ribbon_mapsto_exclusive `{!AntiSymm (=) steps} γ i s1 s2 :
      ribbon_mapsto γ i 1 s1 -∗
      ribbon_mapsto γ i 1 s2 -∗
      False.
    Proof.
      iIntros "Hmapsto1 Hmapsto2".
      iDestruct (ribbon_mapsto_valid_2 with "Hmapsto1 Hmapsto2") as "(% & _)". done.
    Qed.

    Lemma ribbon_auth_mapsto_valid `{!AntiSymm (=) steps} γ dq rib i q s :
      ribbon_auth γ dq rib -∗
      ribbon_mapsto γ i q s -∗
      ⌜rib !! i = Some s⌝.
    Proof.
      iIntros "Hauth Hmapsto".
      iDestruct (own_valid_2 with "Hauth Hmapsto") as %?%ribbon_auth_mapsto_dfrac_valid.
      naive_solver.
    Qed.

    Lemma ribbon_auth_lb_valid γ dq rib i t :
      ribbon_auth γ dq rib -∗
      ribbon_lb γ i t -∗
      ⌜∃ s, rib !! i = Some s ∧ steps t s⌝.
    Proof.
      iIntros "Hauth Hlb".
      iDestruct (own_valid_2 with "Hauth Hlb") as %?%ribbon_auth_dfrac_lb_valid.
      naive_solver.
    Qed.

    Lemma ribbon_mapsto_lb_valid γ i q s t :
      ribbon_mapsto γ i q s -∗
      ribbon_lb γ i t -∗
      ⌜steps t s⌝.
    Proof.
      iIntros "Hmapsto Hlb".
      iDestruct (own_valid_2 with "Hmapsto Hlb") as %?%ribbon_mapsto_frac_lb_valid.
      naive_solver.
    Qed.

    Lemma ribbon_lb_get γ i q s :
      ribbon_mapsto γ i q s -∗
      ribbon_lb γ i s.
    Proof.
      apply own_mono, ribbon_lb_included.
    Qed.
    Lemma ribbon_lb_mono {γ i s} s' :
      steps s' s →
      ribbon_lb γ i s -∗
      ribbon_lb γ i s'.
    Proof.
      intros. apply own_mono, ribbon_lb_mono. done.
    Qed.

    Lemma ribbon_auth_persist γ dq rib :
      ribbon_auth γ dq rib ==∗
      ribbon_auth γ DfracDiscarded rib.
    Proof.
      iApply own_update. apply ribbon_auth_persist.
    Qed.
    Lemma ribbon_auth_alloc {γ rib} s :
      ribbon_auth γ (DfracOwn 1) rib ==∗
      ribbon_auth γ (DfracOwn 1) (rib ++ [s]).
    Proof.
      iIntros "Hauth".
      iMod (own_update with "Hauth"); first apply ribbon_auth_alloc; done.
    Qed.

    Lemma ribbon_update `{!AntiSymm (=) steps} {γ rib i s} s' :
      steps s s' →
      ribbon_auth γ (DfracOwn 1) rib -∗
      ribbon_mapsto γ i 1 s ==∗
        ribbon_auth γ (DfracOwn 1) (<[i := s']> rib) ∗
        ribbon_mapsto γ i 1 s'.
    Proof.
      iIntros "% Hauth Hmapsto".
      iMod (own_update_2 with "Hauth Hmapsto") as "($ & $)"; first apply ribbon_update; done.
    Qed.
  End ribbon_G.
End sts.

#[global] Opaque ribbon_auth.
#[global] Opaque ribbon_mapsto.
#[global] Opaque ribbon_lb.
