From iris.algebra Require Import
  gmap
  proofmode_classes.

From caml5 Require Import
  prelude.
From caml5.algebra Require Export
  base.
From caml5.algebra Require Import
  auth
  lib.sts_cell.

Section sts.
  Context key `{Countable key}.
  Context `(step : relation state).

  Definition sts_cells :=
    auth (gmapUR key (sts_cell_UR step)).
  Definition sts_cells_R :=
    authR (gmapUR key (sts_cell_UR step)).
  Definition sts_cells_UR :=
    authUR (gmapUR key (sts_cell_UR step)).
End sts.

Section sts.
  Context `{Countable key}.
  Context `(step : relation state).
  Implicit Types k : key.
  Implicit Types s : state.
  Implicit Types ss : gmap key state.

  Let state_O := leibnizO state.
  #[local] Canonical state_O.

  Notation steps := (rtc step).

  Definition sts_cells_auth dq ss : sts_cells_UR key step :=
    ●{dq} (sts_cell_auth step (DfracOwn 1) <$> ss).
  Definition sts_cells_mapsto k q s : sts_cells_UR key step :=
    ◯ {[k := sts_cell_auth step (DfracOwn q) s]}.
  Definition sts_cells_lb k s : sts_cells_UR key step :=
    ◯ {[k := sts_cell_lb step s]}.

  #[global] Instance sts_cells_cmra_discrete :
    CmraDiscrete (sts_cells_R key step).
  Proof.
    apply _.
  Qed.

  #[global] Instance sts_cells_auth_core_id ss :
    CoreId (sts_cells_auth DfracDiscarded ss).
  Proof.
    apply _.
  Qed.
  #[global] Instance sts_cells_lb_core_id k s :
    CoreId (sts_cells_lb k s).
  Proof.
    apply _.
  Qed.

  Lemma sts_cells_auth_dfrac_op dq1 dq2 ss :
    sts_cells_auth (dq1 ⋅ dq2) ss ≡ sts_cells_auth dq1 ss ⋅ sts_cells_auth dq2 ss.
  Proof.
    apply auth_auth_dfrac_op.
  Qed.
  #[global] Instance sts_cells_auth_dfrac_is_op dq dq1 dq2 ss :
    IsOp dq dq1 dq2 →
    IsOp' (sts_cells_auth dq ss) (sts_cells_auth dq1 ss) (sts_cells_auth dq2 ss).
  Proof.
    apply _.
  Qed.

  Lemma sts_cells_mapsto_op k q1 q2 s :
    sts_cells_mapsto k (q1 ⋅ q2) s ≡ sts_cells_mapsto k q1 s ⋅ sts_cells_mapsto k q2 s.
  Proof.
    apply is_op, _.
  Qed.
  #[global] Instance sts_cells_mapsto_frac_is_op k q q1 q2 s :
    IsOp q q1 q2 →
    IsOp' (sts_cells_mapsto k q s) (sts_cells_mapsto k q1 s) (sts_cells_mapsto k q2 s).
  Proof.
    apply _.
  Qed.

  Lemma sts_cells_mapsto_lb_op k q s :
    sts_cells_mapsto k q s ≡ sts_cells_mapsto k q s ⋅ sts_cells_lb k s.
  Proof.
    rewrite /sts_cells_mapsto /sts_cells_lb -auth_frag_op. f_equiv.
    rewrite singleton_op singletonM_proper // -sts_cell_auth_frag_op //.
  Qed.

  Lemma sts_cells_auth_dfrac_valid dq ss :
    ✓ sts_cells_auth dq ss ↔
    ✓ dq.
  Proof.
    rewrite auth_auth_dfrac_valid. split; first naive_solver. intros. split; first done.
    intros k. rewrite lookup_fmap. destruct (ss !! k) eqn:?; last done.
    apply Some_valid, sts_cell_auth_valid.
  Qed.
  Lemma sts_cells_auth_valid ss :
    ✓ sts_cells_auth (DfracOwn 1) ss.
  Proof.
    rewrite sts_cells_auth_dfrac_valid //.
  Qed.

  Lemma sts_cells_mapsto_dfrac_valid k q s :
    ✓ sts_cells_mapsto k q s ↔
    ✓ q.
  Proof.
    rewrite auth_frag_valid singleton_valid sts_cell_auth_dfrac_valid //.
  Qed.
  Lemma sts_cells_mapsto_valid k s :
    ✓ sts_cells_mapsto k 1 s.
  Proof.
    rewrite sts_cells_mapsto_dfrac_valid //.
  Qed.

  Lemma sts_cells_auth_dfrac_op_valid `{!AntiSymm (=) steps} dq1 ss1 dq2 ss2 :
    ✓ (sts_cells_auth dq1 ss1 ⋅ sts_cells_auth dq2 ss2) ↔
    ✓ (dq1 ⋅ dq2) ∧ ss1 = ss2.
  Proof.
    rewrite auth_auth_dfrac_op_valid. split.
    - intros (? & ?%(@inj _ _ (≡) (≡) (fmap (sts_cell_auth step (DfracOwn 1))) _) & _).
      naive_solver.
    - intros (? & ->). split_and!; try done.
      intros k. rewrite lookup_fmap. destruct (ss2 !! k) eqn:?; last done.
      apply Some_valid, sts_cell_auth_valid.
  Qed.
  Lemma sts_cells_auth_op_valid `{!AntiSymm (=) steps} ss1 ss2 :
    ✓ (sts_cells_auth (DfracOwn 1) ss1 ⋅ sts_cells_auth (DfracOwn 1) ss2) ↔
    False.
  Proof.
    rewrite sts_cells_auth_dfrac_op_valid. naive_solver.
  Qed.

  Lemma sts_cells_mapsto_dfrac_op_valid `{!AntiSymm (=) steps} k q1 s1 q2 s2 :
    ✓ (sts_cells_mapsto k q1 s1 ⋅ sts_cells_mapsto k q2 s2) ↔
    ✓ (q1 ⋅ q2) ∧ s1 = s2.
  Proof.
    rewrite auth_frag_op_valid singleton_op singleton_valid sts_cell_auth_dfrac_op_valid //.
  Qed.
  Lemma sts_cells_mapsto_op_valid `{!AntiSymm (=) steps} k s1 s2 :
    ✓ (sts_cells_mapsto k 1 s1 ⋅ sts_cells_mapsto k 1 s2) ↔
    False.
  Proof.
    rewrite sts_cells_mapsto_dfrac_op_valid. naive_solver.
  Qed.

  Lemma sts_cells_auth_frag_dfrac_valid `{!AntiSymm (=) steps} dq ss k q s :
    ✓ (sts_cells_auth dq ss ⋅ sts_cells_mapsto k q s) ↔
    ✓ dq ∧ ✓ q ∧ ss !! k = Some s.
  Proof.
    rewrite auth_both_dfrac_valid_discrete singleton_included_l frac_valid.
    setoid_rewrite Some_equiv_eq.
    setoid_rewrite lookup_fmap_Some.
    setoid_rewrite Some_included_total.
    split.
    - intros (Hdq & ((? & (? & (_s & <- & Hlookup) & <-) & Hincluded) & _)).
      rewrite sts_cell_auth_dfrac_included in Hincluded. destruct Hincluded as (Hq & <-).
      split_and!; try done. rewrite Qp.le_lteq.
      destruct Hq as [?%dfrac_own_included | ->%(inj DfracOwn)]; naive_solver.
    - intros (Hdq & Hq & Hlookup).
      split; first done. split.
      + exists (sts_cell_auth step (DfracOwn 1) s). split; first naive_solver.
        rewrite sts_cell_auth_dfrac_included dfrac_own_included. split; last done.
        rewrite Qp.le_lteq in Hq. naive_solver.
      + clear. intros k. rewrite lookup_fmap.
        destruct (ss !! k); [apply sts_cell_auth_valid | done].
  Qed.
  Lemma sts_cells_auth_frag_valid `{!AntiSymm (=) steps} ss k s :
    ✓ (sts_cells_auth (DfracOwn 1) ss ⋅ sts_cells_mapsto k 1 s) ↔
    ss !! k = Some s.
  Proof.
    rewrite sts_cells_auth_frag_dfrac_valid. naive_solver apply dfrac_valid_own_1.
  Qed.

  Lemma sts_cells_auth_dfrac_lb_valid dq ss k s :
    ✓ (sts_cells_auth dq ss ⋅ sts_cells_lb k s) ↔
    ✓ dq ∧ ∃ s', steps s s' ∧ ss !! k = Some s'.
  Proof.
    rewrite auth_both_dfrac_valid_discrete singleton_included_l.
    setoid_rewrite Some_equiv_eq.
    setoid_rewrite lookup_fmap_Some.
    setoid_rewrite Some_included_total.
    split.
    - intros (Hdq & ((? & (? & (s' & <- & Hlookup) & <-) & Hincluded) & _)).
      rewrite sts_cell_lb_included in Hincluded. naive_solver.
    - intros (Hdq & (s' & Hsteps & Hlookup)).
      split; first done. split.
      + exists (sts_cell_auth step (DfracOwn 1) s'). split; first naive_solver.
        rewrite sts_cell_lb_included //.
      + clear. intros k. rewrite lookup_fmap.
        destruct (ss !! k); [apply sts_cell_auth_valid | done].
  Qed.
  Lemma sts_cells_auth_lb_valid ss k s :
    ✓ (sts_cells_auth (DfracOwn 1) ss ⋅ sts_cells_lb k s) ↔
    ∃ s', steps s s' ∧ ss !! k = Some s'.
  Proof.
    rewrite sts_cells_auth_dfrac_lb_valid. naive_solver apply dfrac_valid_own_1.
  Qed.

  Lemma sts_cells_mapsto_dfrac_lb_valid k q s1 s2 :
    ✓ (sts_cells_mapsto k q s1 ⋅ sts_cells_lb k s2) ↔
    ✓ q ∧ steps s2 s1.
  Proof.
    rewrite -is_op auth_frag_valid singleton_valid sts_cell_both_dfrac_valid //.
  Qed.
  Lemma sts_cells_mapsto_lb_valid k s1 s2 :
    ✓ (sts_cells_mapsto k 1 s1 ⋅ sts_cells_lb k s2) ↔
    steps s2 s1.
  Proof.
    rewrite sts_cells_mapsto_dfrac_lb_valid. naive_solver apply frac_valid_1.
  Qed.

  Lemma sts_cells_lb_mono k s1 s2 :
    steps s1 s2 →
    sts_cells_lb k s1 ≼ sts_cells_lb k s2.
  Proof.
    intros. apply auth_frag_mono, singleton_included.
    right. apply sts_cell_lb_mono. done.
  Qed.

  Lemma sts_cells_lb_included k dq s :
    sts_cells_lb k s ≼ sts_cells_mapsto k dq s.
  Proof.
    apply auth_frag_mono, singleton_included.
    right. apply sts_cell_lb_included'.
  Qed.

  Lemma sts_cells_auth_persist dq ss :
    sts_cells_auth dq ss ~~> sts_cells_auth DfracDiscarded ss.
  Proof.
    apply auth_update_auth_persist.
  Qed.
  Lemma sts_cells_auth_alloc k s ss :
    ss !! k = None →
    sts_cells_auth (DfracOwn 1) ss ~~> sts_cells_auth (DfracOwn 1) (<[k := s]> ss).
  Proof.
    intros Hlookup.
    etrans; last apply cmra_update_op_l. apply auth_update_alloc.
    rewrite fmap_insert.
    apply alloc_singleton_local_update; last apply sts_cell_auth_valid.
    rewrite lookup_fmap Hlookup //.
  Qed.

  Lemma sts_cells_update `{!AntiSymm (=) steps} {ss k s} s' :
    steps s s' →
    sts_cells_auth (DfracOwn 1) ss ⋅ sts_cells_mapsto k 1 s ~~>
    sts_cells_auth (DfracOwn 1) (<[k := s']> ss) ⋅ sts_cells_mapsto k 1 s'.
  Proof.
    intros.
    apply cmra_update_valid0. intros Hlookup%cmra_discrete_valid%sts_cells_auth_frag_valid.
    apply auth_update. rewrite fmap_insert. apply singleton_local_update_any.
    intros ? (? & <- & ?)%lookup_fmap_Some. simplify_eq.
    apply sts_cell_auth_local_update. done.
  Qed.
End sts.

#[global] Opaque sts_cells_auth.
#[global] Opaque sts_cells_mapsto.
#[global] Opaque sts_cells_lb.
