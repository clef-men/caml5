From iris.proofmode Require Import
  proofmode.

From caml5 Require Import
  prelude.
From caml5 Require Export
  base.
From caml5.common Require Import
  tactics.
From caml5.base_logic Require Import
  lib.ribbon.

Inductive simple_ribbon_state {val : Type} :=
  | SimpleRibbonEmpty
  | SimpleRibbonSet (v : val)
  | SimpleRibbonFree.
#[global] Arguments simple_ribbon_state : clear implicits.

Inductive simple_ribbon_step {val} : simple_ribbon_state val → simple_ribbon_state val → Prop :=
  | simple_ribbon_step_set v :
      simple_ribbon_step SimpleRibbonEmpty (SimpleRibbonSet v)
  | simple_ribbon_step_free v :
      simple_ribbon_step (SimpleRibbonSet v) SimpleRibbonFree.
#[global] Arguments simple_ribbon_step : clear implicits.

Definition simple_ribbon_steps val :=
  rtc (simple_ribbon_step val).

Ltac invert_simple_ribbon_steps :=
  repeat match goal with
  | H: simple_ribbon_step _ _ _ |- _ => invert H
  | H: simple_ribbon_steps _ _ _ |- _ => invert H
  | H: rtc (simple_ribbon_step _) _ _ |- _ => invert H
  end.

#[global] Instance simple_ribbon_steps_antisymm val :
  AntiSymm (=) (simple_ribbon_steps val).
Proof.
  intros s1 s2 Hsteps1 Hsteps2. destruct s1, s2; invert_simple_ribbon_steps; done.
Qed.

Class SimpleRibbonG Σ val := {
  simple_ribbon_G_ribbon_G : RibbonG (simple_ribbon_step val) Σ ;
}.
#[global] Arguments SimpleRibbonG : clear implicits.
#[local] Existing Instance simple_ribbon_G_ribbon_G.

Definition simple_ribbon_Σ val := #[
  ribbon_Σ (simple_ribbon_step val)
].
#[global] Instance subG_ribbon_Σ Σ val :
  subG (simple_ribbon_Σ val) Σ →
  SimpleRibbonG Σ val.
Proof.
  solve_inG.
Qed.

Section simple_ribbon_G.
  Context `{simple_ribbon_G : !SimpleRibbonG Σ val}.

  Definition simple_ribbon_auth γ dq rib :=
    ribbon_auth (simple_ribbon_step val) γ dq rib.
  Definition simple_ribbon_mapsto γ i q s :=
    ribbon_mapsto (simple_ribbon_step val) γ i q s.
  Definition simple_ribbon_lb γ i s :=
    ribbon_lb (simple_ribbon_step val) γ i s.

  #[global] Instance simple_ribbon_auth_timeless γ dq rib :
    Timeless (simple_ribbon_auth γ dq rib).
  Proof.
    apply _.
  Qed.
  #[global] Instance simple_ribbon_auth_persistent γ rib :
    Persistent (simple_ribbon_auth γ DfracDiscarded rib).
  Proof.
    apply _.
  Qed.
  #[global] Instance simple_ribbon_mapsto_timeless γ i q s :
    Timeless (simple_ribbon_mapsto γ i q s).
  Proof.
    apply _.
  Qed.
  #[global] Instance simple_ribbon_lb_timeless γ i s :
    Timeless (simple_ribbon_lb γ i s).
  Proof.
    apply _.
  Qed.
  #[global] Instance simple_ribbon_lb_persistent γ i s :
    Persistent (simple_ribbon_lb γ i s).
  Proof.
    apply _.
  Qed.

  #[global] Instance simple_ribbon_auth_fractional γ rib :
    Fractional (λ q, simple_ribbon_auth γ (DfracOwn q) rib).
  Proof.
    apply _.
  Qed.
  #[global] Instance simple_ribbon_auth_as_fractional γ q rib :
    AsFractional (simple_ribbon_auth γ (DfracOwn q) rib) (λ q, simple_ribbon_auth γ (DfracOwn q) rib) q.
  Proof.
    apply _.
  Qed.
  #[global] Instance simple_ribbon_mapsto_fractional γ i s :
    Fractional (λ q, simple_ribbon_mapsto γ i q s).
  Proof.
    apply _.
  Qed.
  #[global] Instance simple_ribbon_mapsto_as_fractional γ i q s :
    AsFractional (simple_ribbon_mapsto γ i q s) (λ q, simple_ribbon_mapsto γ i q s) q.
  Proof.
    apply _.
  Qed.

  Lemma simple_ribbon_alloc :
    ⊢ |==> ∃ γ,
      simple_ribbon_auth γ (DfracOwn 1) [].
  Proof.
    apply ribbon_alloc.
  Qed.

  Lemma simple_ribbon_auth_valid γ dq rib :
    simple_ribbon_auth γ dq rib -∗
    ⌜✓ dq⌝.
  Proof.
    apply ribbon_auth_valid.
  Qed.
  Lemma simple_ribbon_auth_combine γ dq1 rib1 dq2 rib2 :
    simple_ribbon_auth γ dq1 rib1 -∗
    simple_ribbon_auth γ dq2 rib2 -∗
      simple_ribbon_auth γ (dq1 ⋅ dq2) rib1 ∗
      ⌜rib1 = rib2⌝.
  Proof.
    apply ribbon_auth_combine, _.
  Qed.
  Lemma simple_ribbon_auth_valid_2 γ dq1 rib1 dq2 rib2 :
    simple_ribbon_auth γ dq1 rib1 -∗
    simple_ribbon_auth γ dq2 rib2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ rib1 = rib2⌝.
  Proof.
    apply ribbon_auth_valid_2, _.
  Qed.
  Lemma simple_ribbon_auth_agree γ dq1 rib1 dq2 rib2 :
    simple_ribbon_auth γ dq1 rib1 -∗
    simple_ribbon_auth γ dq2 rib2 -∗
    ⌜rib1 = rib2⌝.
  Proof.
    apply ribbon_auth_agree, _.
  Qed.
  Lemma simple_ribbon_auth_exclusive γ rib1 rib2 :
    simple_ribbon_auth γ (DfracOwn 1) rib1 -∗
    simple_ribbon_auth γ (DfracOwn 1) rib2 -∗
    False.
  Proof.
    apply ribbon_auth_exclusive, _.
  Qed.

  Lemma simple_ribbon_mapsto_valid γ i q s :
    simple_ribbon_mapsto γ i q s -∗
    ⌜✓ q⌝.
  Proof.
    apply ribbon_mapsto_valid.
  Qed.
  Lemma simple_ribbon_mapsto_combine γ i q1 s1 q2 s2 :
    simple_ribbon_mapsto γ i q1 s1 -∗
    simple_ribbon_mapsto γ i q2 s2 -∗
      simple_ribbon_mapsto γ i (q1 ⋅ q2) s1 ∗
      ⌜s1 = s2⌝.
  Proof.
    apply ribbon_mapsto_combine, _.
  Qed.
  Lemma simple_ribbon_mapsto_valid_2 γ i q1 s1 q2 s2 :
    simple_ribbon_mapsto γ i q1 s1 -∗
    simple_ribbon_mapsto γ i q2 s2 -∗
    ⌜✓ (q1 ⋅ q2) ∧ s1 = s2⌝.
  Proof.
    apply ribbon_mapsto_valid_2, _.
  Qed.
  Lemma simple_ribbon_mapsto_agree γ i q1 s1 q2 s2 :
    simple_ribbon_mapsto γ i q1 s1 -∗
    simple_ribbon_mapsto γ i q2 s2 -∗
    ⌜s1 = s2⌝.
  Proof.
    apply ribbon_mapsto_agree, _.
  Qed.
  Lemma simple_ribbon_mapsto_exclusive γ i s1 s2 :
    simple_ribbon_mapsto γ i 1 s1 -∗
    simple_ribbon_mapsto γ i 1 s2 -∗
    False.
  Proof.
    apply ribbon_mapsto_exclusive, _.
  Qed.

  Lemma simple_ribbon_auth_mapsto_valid γ dq rib i q s :
    simple_ribbon_auth γ dq rib -∗
    simple_ribbon_mapsto γ i q s -∗
    ⌜rib !! i = Some s⌝.
  Proof.
    apply ribbon_auth_mapsto_valid, _.
  Qed.

  Lemma simple_ribbon_auth_lb_valid γ dq rib i t :
    simple_ribbon_auth γ dq rib -∗
    simple_ribbon_lb γ i t -∗
    ⌜∃ s, rib !! i = Some s ∧ (simple_ribbon_steps val) t s⌝.
  Proof.
    apply ribbon_auth_lb_valid.
  Qed.
  Lemma simple_ribbon_auth_lb_set_valid γ dq rib i v :
    simple_ribbon_auth γ dq rib -∗
    simple_ribbon_lb γ i (SimpleRibbonSet v) -∗
    ⌜∃ s, rib !! i = Some s ∧ (s = SimpleRibbonSet v ∨ s = SimpleRibbonFree)⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (simple_ribbon_auth_lb_valid with "Hauth Hlb") as %(s & Hlookup & Hsteps).
    invert_simple_ribbon_steps; naive_solver.
  Qed.
  Lemma simple_ribbon_auth_lb_free_valid γ dq rib i :
    simple_ribbon_auth γ dq rib -∗
    simple_ribbon_lb γ i SimpleRibbonFree -∗
    ⌜rib !! i = Some SimpleRibbonFree⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (simple_ribbon_auth_lb_valid with "Hauth Hlb") as %(s & Hlookup & Hsteps).
    invert_simple_ribbon_steps; naive_solver.
  Qed.

  Lemma simple_ribbon_mapsto_lb_valid γ i q s t :
    simple_ribbon_mapsto γ i q s -∗
    simple_ribbon_lb γ i t -∗
    ⌜simple_ribbon_steps val t s⌝.
  Proof.
    apply ribbon_mapsto_lb_valid.
  Qed.
  Lemma simple_ribbon_mapsto_lb_set_valid γ i q s v :
    simple_ribbon_mapsto γ i q s -∗
    simple_ribbon_lb γ i (SimpleRibbonSet v) -∗
    ⌜s = SimpleRibbonSet v ∨ s = SimpleRibbonFree⌝.
  Proof.
    iIntros "Hmapsto Hlb".
    iDestruct (simple_ribbon_mapsto_lb_valid with "Hmapsto Hlb") as %Hsteps.
    invert_simple_ribbon_steps; naive_solver.
  Qed.
  Lemma simple_ribbon_mapsto_lb_free_valid γ i q s :
    simple_ribbon_mapsto γ i q s -∗
    simple_ribbon_lb γ i SimpleRibbonFree -∗
    ⌜s = SimpleRibbonFree⌝.
  Proof.
    iIntros "Hmapsto Hlb".
    iDestruct (simple_ribbon_mapsto_lb_valid with "Hmapsto Hlb") as %Hsteps.
    invert_simple_ribbon_steps; naive_solver.
  Qed.

  Lemma simple_ribbon_lb_get γ i q s :
    simple_ribbon_mapsto γ i q s -∗
    simple_ribbon_lb γ i s.
  Proof.
    apply ribbon_lb_get.
  Qed.
  Lemma simple_ribbon_lb_mono {γ i s} s' :
    simple_ribbon_steps val s' s →
    simple_ribbon_lb γ i s -∗
    simple_ribbon_lb γ i s'.
  Proof.
    apply ribbon_lb_mono.
  Qed.

  Lemma simple_ribbon_auth_persist γ dq rib :
    simple_ribbon_auth γ dq rib ==∗
    simple_ribbon_auth γ DfracDiscarded rib.
  Proof.
    apply ribbon_auth_persist.
  Qed.
  Lemma simple_ribbon_auth_alloc {γ rib} s :
    simple_ribbon_auth γ (DfracOwn 1) rib ==∗
    simple_ribbon_auth γ (DfracOwn 1) (rib ++ [s]).
  Proof.
    apply ribbon_auth_alloc.
  Qed.

  Lemma simple_ribbon_update {γ rib i s} s' :
    simple_ribbon_steps val s s' →
    simple_ribbon_auth γ (DfracOwn 1) rib -∗
    simple_ribbon_mapsto γ i 1 s ==∗
      simple_ribbon_auth γ (DfracOwn 1) (<[i := s']> rib) ∗
      simple_ribbon_mapsto γ i 1 s'.
  Proof.
    apply ribbon_update, _.
  Qed.
  Lemma simple_ribbon_set {γ rib i} v :
    simple_ribbon_auth γ (DfracOwn 1) rib -∗
    simple_ribbon_mapsto γ i 1 SimpleRibbonEmpty ==∗
      simple_ribbon_auth γ (DfracOwn 1) (<[i := SimpleRibbonSet v]> rib) ∗
      simple_ribbon_mapsto γ i 1 (SimpleRibbonSet v).
  Proof.
    apply simple_ribbon_update, rtc_once. constructor.
  Qed.
  Lemma simple_ribbon_free {γ rib i} v :
    simple_ribbon_auth γ (DfracOwn 1) rib -∗
    simple_ribbon_mapsto γ i 1 (SimpleRibbonSet v) ==∗
      simple_ribbon_auth γ (DfracOwn 1) (<[i := SimpleRibbonFree]> rib) ∗
      simple_ribbon_mapsto γ i 1 SimpleRibbonFree.
  Proof.
    apply simple_ribbon_update, rtc_once. constructor.
  Qed.
End simple_ribbon_G.

#[global] Opaque simple_ribbon_auth.
#[global] Opaque simple_ribbon_mapsto.
#[global] Opaque simple_ribbon_lb.
