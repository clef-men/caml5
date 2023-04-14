From stdpp Require Import
  gmap.

From iris.algebra Require Import
  proofmode_classes.

From caml5 Require Import
  prelude.
From caml5.common Require Import
  fin_maps.
From caml5.algebra Require Export
  base.
From caml5.algebra Require Import
  lib.sts_cells.

Section sts.
  Context {state} (step : relation state).
  Implicit Types i : nat.
  Implicit Types s : state.
  Implicit Types rib : list state.

  Notation steps := (rtc step).

  Definition ribbon :=
    sts_cells nat step.
  Definition ribbon_R :=
    sts_cells_R nat step.
  Definition ribbon_UR :=
    sts_cells_UR nat step.

  Definition ribbon_auth dq rib : ribbon_UR :=
    sts_cells_auth step dq (map_seq 0 rib).
  Definition ribbon_mapsto i q s : ribbon_UR :=
    sts_cells_mapsto step i q s.
  Definition ribbon_lb i s : ribbon_UR :=
    sts_cells_lb step i s.

  #[global] Instance ribbon_cmra_discrete :
    CmraDiscrete ribbon_R.
  Proof.
    apply _.
  Qed.

  #[global] Instance ribbon_auth_core_id rib :
    CoreId (ribbon_auth DfracDiscarded rib).
  Proof.
    apply _.
  Qed.
  #[global] Instance ribbon_lb_core_id i s :
    CoreId (ribbon_lb i s).
  Proof.
    apply _.
  Qed.

  Lemma ribbon_auth_dfrac_op dq1 dq2 rib :
    ribbon_auth (dq1 ⋅ dq2) rib ≡ ribbon_auth dq1 rib ⋅ ribbon_auth dq2 rib.
  Proof.
    apply sts_cells_auth_dfrac_op.
  Qed.
  #[global] Instance ribbon_auth_dfrac_is_op dq dq1 dq2 rib :
    IsOp dq dq1 dq2 →
    IsOp' (ribbon_auth dq rib) (ribbon_auth dq1 rib) (ribbon_auth dq2 rib).
  Proof.
    apply _.
  Qed.

  Lemma ribbon_mapsto_op i q1 q2 s :
    ribbon_mapsto i (q1 ⋅ q2) s ≡ ribbon_mapsto i q1 s ⋅ ribbon_mapsto i q2 s.
  Proof.
    apply sts_cells_mapsto_op.
  Qed.
  #[global] Instance ribbon_mapsto_frac_is_op i q q1 q2 s :
    IsOp q q1 q2 →
    IsOp' (ribbon_mapsto i q s) (ribbon_mapsto i q1 s) (ribbon_mapsto i q2 s).
  Proof.
    apply _.
  Qed.

  Lemma ribbon_mapsto_lb_op i q s :
    ribbon_mapsto i q s ≡ ribbon_mapsto i q s ⋅ ribbon_lb i s.
  Proof.
    apply sts_cells_mapsto_lb_op.
  Qed.

  Lemma ribbon_auth_dfrac_valid dq rib :
    ✓ ribbon_auth dq rib ↔
    ✓ dq.
  Proof.
    apply sts_cells_auth_dfrac_valid.
  Qed.
  Lemma ribbon_auth_valid rib :
    ✓ ribbon_auth (DfracOwn 1) rib.
  Proof.
    apply sts_cells_auth_valid.
  Qed.

  Lemma ribbon_mapsto_dfrac_valid i q s :
    ✓ ribbon_mapsto i q s ↔
    ✓ q.
  Proof.
    apply sts_cells_mapsto_dfrac_valid.
  Qed.
  Lemma ribbon_mapsto_valid i s :
    ✓ ribbon_mapsto i 1 s.
  Proof.
    apply sts_cells_mapsto_valid.
  Qed.

  Lemma ribbon_auth_dfrac_op_valid `{!AntiSymm (=) steps} dq1 rib1 dq2 rib2 :
    ✓ (ribbon_auth dq1 rib1 ⋅ ribbon_auth dq2 rib2) ↔
    ✓ (dq1 ⋅ dq2) ∧ rib1 = rib2.
  Proof.
    rewrite sts_cells_auth_dfrac_op_valid. split; last naive_solver.
    intros (? & ?%(inj _)). done.
  Qed.
  Lemma ribbon_auth_op_valid `{!AntiSymm (=) steps} rib1 rib2 :
    ✓ (ribbon_auth (DfracOwn 1) rib1 ⋅ ribbon_auth (DfracOwn 1) rib2) ↔
    False.
  Proof.
    rewrite ribbon_auth_dfrac_op_valid. naive_solver.
  Qed.

  Lemma ribbon_mapsto_dfrac_op_valid `{!AntiSymm (=) steps} i q1 s1 q2 s2 :
    ✓ (ribbon_mapsto i q1 s1 ⋅ ribbon_mapsto i q2 s2) ↔
    ✓ (q1 ⋅ q2) ∧ s1 = s2.
  Proof.
    rewrite sts_cells_mapsto_dfrac_op_valid //.
  Qed.
  Lemma ribbon_mapsto_op_valid `{!AntiSymm (=) steps} i s1 s2 :
    ✓ (ribbon_mapsto i 1 s1 ⋅ ribbon_mapsto i 1 s2) ↔
    False.
  Proof.
    rewrite sts_cells_mapsto_op_valid //.
  Qed.

  Lemma ribbon_auth_frag_dfrac_valid `{!AntiSymm (=) steps} dq rib i q s :
    ✓ (ribbon_auth dq rib ⋅ ribbon_mapsto i q s) ↔
    ✓ dq ∧ ✓ q ∧ rib !! i = Some s.
  Proof.
    rewrite sts_cells_auth_frag_dfrac_valid (lookup_map_seq_Some_inv 0) //.
  Qed.
  Lemma ribbon_auth_frag_valid `{!AntiSymm (=) steps} rib i s :
    ✓ (ribbon_auth (DfracOwn 1) rib ⋅ ribbon_mapsto i 1 s) ↔
    rib !! i = Some s.
  Proof.
    rewrite ribbon_auth_frag_dfrac_valid. naive_solver apply dfrac_valid_own_1.
  Qed.

  Lemma ribbon_auth_dfrac_lb_valid dq rib i s :
    ✓ (ribbon_auth dq rib ⋅ ribbon_lb i s) ↔
    ✓ dq ∧ ∃ s', steps s s' ∧ rib !! i = Some s'.
  Proof.
    rewrite sts_cells_auth_dfrac_lb_valid.
    setoid_rewrite (lookup_map_seq_Some_inv 0). done.
  Qed.
  Lemma ribbon_auth_lb_valid rib i s :
    ✓ (ribbon_auth (DfracOwn 1) rib ⋅ ribbon_lb i s) ↔
    ∃ s', steps s s' ∧ rib !! i = Some s'.
  Proof.
    rewrite ribbon_auth_dfrac_lb_valid. naive_solver apply dfrac_valid_own_1.
  Qed.

  Lemma ribbon_mapsto_dfrac_lb_valid i q s1 s2 :
    ✓ (ribbon_mapsto i q s1 ⋅ ribbon_lb i s2) ↔
    ✓ q ∧ steps s2 s1.
  Proof.
    rewrite sts_cells_mapsto_dfrac_lb_valid //.
  Qed.
  Lemma ribbon_mapsto_lb_valid i s1 s2 :
    ✓ (ribbon_mapsto i 1 s1 ⋅ ribbon_lb i s2) ↔
    steps s2 s1.
  Proof.
    rewrite sts_cells_mapsto_lb_valid //.
  Qed.

  Lemma ribbon_lb_mono i s1 s2 :
    steps s1 s2 →
    ribbon_lb i s1 ≼ ribbon_lb i s2.
  Proof.
    apply sts_cells_lb_mono.
  Qed.

  Lemma ribbon_lb_included i dq s :
    ribbon_lb i s ≼ ribbon_mapsto i dq s.
  Proof.
    apply sts_cells_lb_included.
  Qed.

  Lemma ribbon_auth_persist dq rib :
    ribbon_auth dq rib ~~> ribbon_auth DfracDiscarded rib.
  Proof.
    apply sts_cells_auth_persist.
  Qed.
  Lemma ribbon_auth_alloc s rib :
    ribbon_auth (DfracOwn 1) rib ~~> ribbon_auth (DfracOwn 1) (rib ++ [s]).
  Proof.
    rewrite /ribbon_auth map_seq_snoc.
    apply sts_cells_auth_alloc. rewrite lookup_map_seq_None. lia.
  Qed.

  Lemma ribbon_update `{!AntiSymm (=) steps} {rib i s} s' :
    steps s s' →
    ribbon_auth (DfracOwn 1) rib ⋅ ribbon_mapsto i 1 s ~~>
    ribbon_auth (DfracOwn 1) (<[i := s']> rib) ⋅ ribbon_mapsto i 1 s'.
  Proof.
    intros.
    apply cmra_update_valid0. intros ?%cmra_discrete_valid%ribbon_auth_frag_valid%lookup_lt_Some.
    rewrite /ribbon_auth -insert_map_seq_0 //.
    apply sts_cells_update; done.
  Qed.
End sts.

#[global] Opaque ribbon_auth.
#[global] Opaque ribbon_mapsto.
#[global] Opaque ribbon_lb.
