From iris.algebra Require Import
  proofmode_classes.

From caml5 Require Import
  prelude.
From caml5.algebra Require Export
  base.
From caml5.algebra Require Import
  auth
  monotone.

Section sts.
  Context `(step : relation state).
  Implicit Types s t : state.

  Let state_O := leibnizO state.
  #[local] Canonical state_O.

  Notation steps := (rtc step).

  Definition sts_cell :=
    auth (mra steps).
  Definition sts_cell_R :=
    authR (mraUR steps).
  Definition sts_cell_UR :=
    authUR (mraUR steps).

  Definition sts_cell_auth dq s :=
    ●{dq} principal steps s ⋅ ◯ principal steps s.
  Definition sts_cell_frag s :=
    ◯ principal steps s.

  #[global] Instance sts_cell_auth_inj `{!AntiSymm (=) steps} :
    Inj2 (=) (=) (≡) sts_cell_auth.
  Proof.
    rewrite /Inj2. setoid_rewrite auth_auth_frag_dfrac_op.
    intros * (-> & ->%(@inj _ _ (≡) _ _ _) & _). done.
  Qed.
  #[global] Instance sts_cell_frag_inj `{!AntiSymm (=) steps} :
    Inj (=) (≡) sts_cell_frag.
  Proof.
    intros s1 s2 ->%(inj auth_frag)%(@inj _ _ (≡) _ _ _). done.
  Qed.

  #[global] Instance sts_cell_cmra_discrete :
    CmraDiscrete sts_cell_R.
  Proof.
    apply _.
  Qed.

  #[global] Instance sts_cell_auth_core_id s :
    CoreId (sts_cell_auth DfracDiscarded s).
  Proof.
    apply _.
  Qed.
  #[global] Instance sts_cell_frag_core_id s :
    CoreId (sts_cell_frag s).
  Proof.
    apply _.
  Qed.

  Lemma sts_cell_auth_dfrac_op dq1 dq2 s :
    sts_cell_auth (dq1 ⋅ dq2) s ≡ sts_cell_auth dq1 s ⋅ sts_cell_auth dq2 s.
  Proof.
    rewrite /sts_cell_auth auth_auth_dfrac_op.
    rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)) -core_id_dup (comm _ (◯ _)) //.
  Qed.
  #[global] Instance sts_cell_auth_dfrac_is_op dq dq1 dq2 s :
    IsOp dq dq1 dq2 →
    IsOp' (sts_cell_auth dq s) (sts_cell_auth dq1 s) (sts_cell_auth dq2 s).
  Proof.
    rewrite /IsOp' /IsOp => ->. rewrite sts_cell_auth_dfrac_op //.
  Qed.

  Lemma sts_cell_frag_op s s' :
    steps s s' →
    sts_cell_frag s' ≡ sts_cell_frag s ⋅ sts_cell_frag s'.
  Proof.
    intros. rewrite -auth_frag_op principal_R_op //.
  Qed.

  Lemma sts_cell_auth_frag_op dq s :
    sts_cell_auth dq s ≡ sts_cell_auth dq s ⋅ sts_cell_frag s.
  Proof.
    rewrite /sts_cell_auth /sts_cell_frag.
    rewrite -!assoc -auth_frag_op -core_id_dup //.
  Qed.

  Lemma sts_cell_auth_dfrac_valid dq s :
    ✓ sts_cell_auth dq s ↔
    ✓ dq.
  Proof.
    rewrite auth_both_dfrac_valid_discrete /=. naive_solver.
  Qed.
  Lemma sts_cell_auth_valid s :
    ✓ sts_cell_auth (DfracOwn 1) s.
  Proof.
    rewrite sts_cell_auth_dfrac_valid //.
  Qed.

  Lemma sts_cell_auth_dfrac_op_valid `{!AntiSymm (=) steps} dq1 s1 dq2 s2 :
    ✓ (sts_cell_auth dq1 s1 ⋅ sts_cell_auth dq2 s2) ↔
    ✓ (dq1 ⋅ dq2) ∧ s1 = s2.
  Proof.
    rewrite /sts_cell_auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
    - move => /cmra_valid_op_l /auth_auth_dfrac_op_valid.
      split; last apply (inj (principal steps)); naive_solver.
    - intros [? ->]. rewrite -core_id_dup -auth_auth_dfrac_op.
      apply auth_both_dfrac_valid_discrete. done.
  Qed.
  Lemma sts_cell_auth_op_valid `{!AntiSymm (=) steps} s1 s2 :
    ✓ (sts_cell_auth (DfracOwn 1) s1 ⋅ sts_cell_auth (DfracOwn 1) s2) ↔
    False.
  Proof.
    rewrite sts_cell_auth_dfrac_op_valid. naive_solver.
  Qed.

  Lemma sts_cell_both_dfrac_valid dq s t :
    ✓ (sts_cell_auth dq s ⋅ sts_cell_frag t) ↔
    ✓ dq ∧ steps t s.
  Proof.
    rewrite -assoc -auth_frag_op auth_both_dfrac_valid_discrete. split.
    - intros. split; first naive_solver.
      rewrite -principal_included. etrans; [apply @cmra_included_r | naive_solver].
    - intros. rewrite (comm op) principal_R_op; naive_solver.
  Qed.
  Lemma sts_cell_both_valid s t :
    ✓ (sts_cell_auth (DfracOwn 1) s ⋅ sts_cell_frag t) ↔
    steps t s.
  Proof.
    rewrite sts_cell_both_dfrac_valid dfrac_valid_own. naive_solver.
  Qed.

  Lemma sts_cell_frag_mono s1 s2 :
    steps s1 s2 →
    sts_cell_frag s1 ≼ sts_cell_frag s2.
  Proof.
    intros. apply auth_frag_mono. rewrite principal_included //.
  Qed.

  Lemma sts_cell_auth_dfrac_included `{!AntiSymm (=) steps} dq1 s1 dq2 s2 :
    sts_cell_auth dq1 s1 ≼ sts_cell_auth dq2 s2 ↔
    (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ s1 = s2.
  Proof.
    rewrite auth_both_dfrac_included principal_included. split; last naive_solver.
    intros (? & ->%(@inj _ _ (≡) _ _ _) & ?). done.
  Qed.
  Lemma sts_cell_auth_included `{!AntiSymm (=) steps} s1 s2 :
    sts_cell_auth (DfracOwn 1) s1 ≼ sts_cell_auth (DfracOwn 1) s2 ↔
    s1 = s2.
  Proof.
    rewrite sts_cell_auth_dfrac_included. naive_solver.
  Qed.

  Lemma sts_cell_frag_included s1 dq s2 :
    sts_cell_frag s1 ≼ sts_cell_auth dq s2 ↔
    steps s1 s2.
  Proof.
    rewrite auth_frag_included principal_included //.
  Qed.
  Lemma sts_cell_frag_included' s dq :
    sts_cell_frag s ≼ sts_cell_auth dq s.
  Proof.
    rewrite sts_cell_frag_included //.
  Qed.

  Lemma sts_cell_auth_persist dq s :
    sts_cell_auth dq s ~~> sts_cell_auth DfracDiscarded s.
  Proof.
    eapply cmra_update_op_proper; last done.
    eapply auth_update_auth_persist.
  Qed.
  Lemma sts_cell_auth_update {s} s' :
    steps s s' →
    sts_cell_auth (DfracOwn 1) s ~~> sts_cell_auth (DfracOwn 1) s'.
  Proof.
    intros. apply auth_update, mra_local_update_grow. done.
  Qed.

  Lemma sts_cell_auth_local_update s s' :
    steps s s' →
    (sts_cell_auth (DfracOwn 1) s, sts_cell_auth (DfracOwn 1) s) ~l~>
    (sts_cell_auth (DfracOwn 1) s', sts_cell_auth (DfracOwn 1) s').
  Proof.
    intros. apply auth_local_update.
    - apply mra_local_update_grow. done.
    - rewrite principal_included //.
    - done.
  Qed.
End sts.

#[global] Opaque sts_cell_auth.
#[global] Opaque sts_cell_frag.
