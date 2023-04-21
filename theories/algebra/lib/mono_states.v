From iris.algebra Require Import
  gmap
  proofmode_classes.

From caml5 Require Import
  prelude.
From caml5.algebra Require Export
  base.
From caml5.algebra Require Import
  auth
  lib.mono_state.

Section sts.
  Context key `{Countable key}.
  Context `(step : relation state).

  Definition mono_states :=
    auth (gmapUR key (mono_state_UR step)).
  Definition mono_states_R :=
    authR (gmapUR key (mono_state_UR step)).
  Definition mono_states_UR :=
    authUR (gmapUR key (mono_state_UR step)).
End sts.

Section sts.
  Context `{Countable key}.
  Context `(step : relation state).
  Implicit Types k : key.
  Implicit Types s t : state.
  Implicit Types ss : gmap key state.

  Let state_O := leibnizO state.
  #[local] Canonical state_O.

  Notation steps := (rtc step).

  Definition mono_states_auth dq ss : mono_states_UR key step :=
    ●{dq} (mono_state_auth step (DfracOwn 1) <$> ss).
  Definition mono_states_mapsto k q s : mono_states_UR key step :=
    ◯ {[k := mono_state_auth step (DfracOwn q) s]}.
  Definition mono_states_lb k s : mono_states_UR key step :=
    ◯ {[k := mono_state_lb step s]}.

  #[global] Instance mono_states_cmra_discrete :
    CmraDiscrete (mono_states_R key step).
  Proof.
    apply _.
  Qed.

  #[global] Instance mono_states_auth_core_id ss :
    CoreId (mono_states_auth DfracDiscarded ss).
  Proof.
    apply _.
  Qed.
  #[global] Instance mono_states_lb_core_id k s :
    CoreId (mono_states_lb k s).
  Proof.
    apply _.
  Qed.

  Lemma mono_states_auth_dfrac_op dq1 dq2 ss :
    mono_states_auth (dq1 ⋅ dq2) ss ≡ mono_states_auth dq1 ss ⋅ mono_states_auth dq2 ss.
  Proof.
    apply auth_auth_dfrac_op.
  Qed.
  #[global] Instance mono_states_auth_dfrac_is_op dq dq1 dq2 ss :
    IsOp dq dq1 dq2 →
    IsOp' (mono_states_auth dq ss) (mono_states_auth dq1 ss) (mono_states_auth dq2 ss).
  Proof.
    apply _.
  Qed.

  Lemma mono_states_mapsto_frac_op k q1 q2 s :
    mono_states_mapsto k (q1 ⋅ q2) s ≡ mono_states_mapsto k q1 s ⋅ mono_states_mapsto k q2 s.
  Proof.
    apply is_op, _.
  Qed.
  #[global] Instance mono_states_mapsto_frac_is_op k q q1 q2 s :
    IsOp q q1 q2 →
    IsOp' (mono_states_mapsto k q s) (mono_states_mapsto k q1 s) (mono_states_mapsto k q2 s).
  Proof.
    apply _.
  Qed.

  Lemma mono_states_mapsto_lb_op k q s :
    mono_states_mapsto k q s ≡ mono_states_mapsto k q s ⋅ mono_states_lb k s.
  Proof.
    rewrite /mono_states_mapsto /mono_states_lb -auth_frag_op. f_equiv.
    rewrite singleton_op singletonM_proper // -mono_state_auth_frag_op //.
  Qed.

  Lemma mono_states_auth_dfrac_valid dq ss :
    ✓ mono_states_auth dq ss ↔
    ✓ dq.
  Proof.
    rewrite auth_auth_dfrac_valid. split; first naive_solver. intros. split; first done.
    intros k. rewrite lookup_fmap. destruct (ss !! k) eqn:?; last done.
    apply Some_valid, mono_state_auth_valid.
  Qed.
  Lemma mono_states_auth_valid ss :
    ✓ mono_states_auth (DfracOwn 1) ss.
  Proof.
    rewrite mono_states_auth_dfrac_valid //.
  Qed.

  Lemma mono_states_mapsto_frac_valid k q s :
    ✓ mono_states_mapsto k q s ↔
    ✓ q.
  Proof.
    rewrite auth_frag_valid singleton_valid mono_state_auth_dfrac_valid //.
  Qed.
  Lemma mono_states_mapsto_valid k s :
    ✓ mono_states_mapsto k 1 s.
  Proof.
    rewrite mono_states_mapsto_frac_valid //.
  Qed.

  Lemma mono_states_auth_dfrac_op_valid `{!AntiSymm (=) steps} dq1 ss1 dq2 ss2 :
    ✓ (mono_states_auth dq1 ss1 ⋅ mono_states_auth dq2 ss2) ↔
    ✓ (dq1 ⋅ dq2) ∧ ss1 = ss2.
  Proof.
    rewrite auth_auth_dfrac_op_valid. split.
    - intros (? & ?%(@inj _ _ (≡) (≡) (fmap (mono_state_auth step (DfracOwn 1))) _) & _).
      naive_solver.
    - intros (? & ->). split_and!; try done.
      intros k. rewrite lookup_fmap. destruct (ss2 !! k) eqn:?; last done.
      apply Some_valid, mono_state_auth_valid.
  Qed.
  Lemma mono_states_auth_op_valid `{!AntiSymm (=) steps} ss1 ss2 :
    ✓ (mono_states_auth (DfracOwn 1) ss1 ⋅ mono_states_auth (DfracOwn 1) ss2) ↔
    False.
  Proof.
    rewrite mono_states_auth_dfrac_op_valid. naive_solver.
  Qed.

  Lemma mono_states_mapsto_frac_op_valid `{!AntiSymm (=) steps} k q1 s1 q2 s2 :
    ✓ (mono_states_mapsto k q1 s1 ⋅ mono_states_mapsto k q2 s2) ↔
    ✓ (q1 ⋅ q2) ∧ s1 = s2.
  Proof.
    rewrite auth_frag_op_valid singleton_op singleton_valid mono_state_auth_dfrac_op_valid //.
  Qed.
  Lemma mono_states_mapsto_op_valid `{!AntiSymm (=) steps} k s1 s2 :
    ✓ (mono_states_mapsto k 1 s1 ⋅ mono_states_mapsto k 1 s2) ↔
    False.
  Proof.
    rewrite mono_states_mapsto_frac_op_valid. naive_solver.
  Qed.

  Lemma mono_states_auth_mapsto_dfrac_valid `{!AntiSymm (=) steps} dq ss k q s :
    ✓ (mono_states_auth dq ss ⋅ mono_states_mapsto k q s) ↔
    ✓ dq ∧ ✓ q ∧ ss !! k = Some s.
  Proof.
    rewrite auth_both_dfrac_valid_discrete singleton_included_l frac_valid.
    setoid_rewrite Some_equiv_eq.
    setoid_rewrite lookup_fmap_Some.
    setoid_rewrite Some_included_total.
    split.
    - intros (Hdq & ((? & (? & (_s & <- & Hlookup) & <-) & Hincluded) & _)).
      rewrite mono_state_auth_dfrac_included in Hincluded. destruct Hincluded as (Hq & <-).
      split_and!; try done. rewrite Qp.le_lteq.
      destruct Hq as [?%dfrac_own_included | ->%(inj DfracOwn)]; naive_solver.
    - intros (Hdq & Hq & Hlookup).
      split; first done. split.
      + exists (mono_state_auth step (DfracOwn 1) s). split; first naive_solver.
        rewrite mono_state_auth_dfrac_included dfrac_own_included. split; last done.
        rewrite Qp.le_lteq in Hq. naive_solver.
      + clear. intros k. rewrite lookup_fmap.
        destruct (ss !! k); [apply mono_state_auth_valid | done].
  Qed.
  Lemma mono_states_auth_mapsto_valid `{!AntiSymm (=) steps} ss k s :
    ✓ (mono_states_auth (DfracOwn 1) ss ⋅ mono_states_mapsto k 1 s) ↔
    ss !! k = Some s.
  Proof.
    rewrite mono_states_auth_mapsto_dfrac_valid. naive_solver apply dfrac_valid_own_1.
  Qed.

  Lemma mono_states_auth_dfrac_lb_valid dq ss k t :
    ✓ (mono_states_auth dq ss ⋅ mono_states_lb k t) ↔
    ✓ dq ∧ ∃ s, steps t s ∧ ss !! k = Some s.
  Proof.
    rewrite auth_both_dfrac_valid_discrete singleton_included_l.
    setoid_rewrite Some_equiv_eq.
    setoid_rewrite lookup_fmap_Some.
    setoid_rewrite Some_included_total.
    split.
    - intros (Hdq & ((? & (? & (s' & <- & Hlookup) & <-) & Hincluded) & _)).
      rewrite mono_state_lb_included in Hincluded. naive_solver.
    - intros (Hdq & (s' & Hsteps & Hlookup)).
      split; first done. split.
      + exists (mono_state_auth step (DfracOwn 1) s'). split; first naive_solver.
        rewrite mono_state_lb_included //.
      + clear. intros k. rewrite lookup_fmap.
        destruct (ss !! k); [apply mono_state_auth_valid | done].
  Qed.
  Lemma mono_states_auth_lb_valid ss k t :
    ✓ (mono_states_auth (DfracOwn 1) ss ⋅ mono_states_lb k t) ↔
    ∃ s, steps t s ∧ ss !! k = Some s.
  Proof.
    rewrite mono_states_auth_dfrac_lb_valid. naive_solver apply dfrac_valid_own_1.
  Qed.

  Lemma mono_states_mapsto_frac_lb_valid k q s1 s2 :
    ✓ (mono_states_mapsto k q s1 ⋅ mono_states_lb k s2) ↔
    ✓ q ∧ steps s2 s1.
  Proof.
    rewrite -is_op auth_frag_valid singleton_valid mono_state_both_dfrac_valid //.
  Qed.
  Lemma mono_states_mapsto_lb_valid k s1 s2 :
    ✓ (mono_states_mapsto k 1 s1 ⋅ mono_states_lb k s2) ↔
    steps s2 s1.
  Proof.
    rewrite mono_states_mapsto_frac_lb_valid. naive_solver apply frac_valid_1.
  Qed.

  Lemma mono_states_lb_mono k s1 s2 :
    steps s1 s2 →
    mono_states_lb k s1 ≼ mono_states_lb k s2.
  Proof.
    intros. apply auth_frag_mono, singleton_included.
    right. apply mono_state_lb_mono. done.
  Qed.

  Lemma mono_states_lb_included k dq s :
    mono_states_lb k s ≼ mono_states_mapsto k dq s.
  Proof.
    apply auth_frag_mono, singleton_included.
    right. apply mono_state_lb_included'.
  Qed.

  Lemma mono_states_auth_persist dq ss :
    mono_states_auth dq ss ~~> mono_states_auth DfracDiscarded ss.
  Proof.
    apply auth_update_auth_persist.
  Qed.
  Lemma mono_states_auth_alloc {ss} k s :
    ss !! k = None →
    mono_states_auth (DfracOwn 1) ss ~~> mono_states_auth (DfracOwn 1) (<[k := s]> ss).
  Proof.
    intros Hlookup.
    etrans; last apply cmra_update_op_l. apply auth_update_alloc.
    rewrite fmap_insert.
    apply alloc_singleton_local_update; last apply mono_state_auth_valid.
    rewrite lookup_fmap Hlookup //.
  Qed.

  Lemma mono_states_update `{!AntiSymm (=) steps} {ss k s} s' :
    steps s s' →
    mono_states_auth (DfracOwn 1) ss ⋅ mono_states_mapsto k 1 s ~~>
    mono_states_auth (DfracOwn 1) (<[k := s']> ss) ⋅ mono_states_mapsto k 1 s'.
  Proof.
    intros.
    apply cmra_update_valid0. intros Hlookup%cmra_discrete_valid%mono_states_auth_mapsto_valid.
    apply auth_update. rewrite fmap_insert. apply singleton_local_update_any.
    intros ? (? & <- & ?)%lookup_fmap_Some. simplify_eq.
    apply mono_state_auth_local_update. done.
  Qed.
End sts.

#[global] Opaque mono_states_auth.
#[global] Opaque mono_states_mapsto.
#[global] Opaque mono_states_lb.
