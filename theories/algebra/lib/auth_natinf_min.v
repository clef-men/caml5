From iris.algebra Require Import
  proofmode_classes.

From caml5 Require Import
  prelude.
From caml5.common Require Export
  natinf.
From caml5.algebra Require Export
  base.
From caml5.algebra Require Import
  auth
  natinf_min.

Implicit Types n m p : natinf.

Definition auth_natinf_min :=
  auth natinf_min_UR.
Definition auth_natinf_min_R :=
  authR natinf_min_UR.
Definition auth_natinf_min_UR :=
  authUR natinf_min_UR.

Definition auth_natinf_min_auth dq n : auth_natinf_min_UR :=
  ●{dq} Build_natinf_min n ⋅ ◯ Build_natinf_min n.
Definition auth_natinf_min_ub n : auth_natinf_min_UR :=
  ◯ Build_natinf_min n.

#[global] Instance auth_natinf_min_cmra_discrete :
  CmraDiscrete auth_natinf_min_R.
Proof.
  apply _.
Qed.

#[global] Instance auth_natinf_min_auth_core_id n :
  CoreId (auth_natinf_min_auth DfracDiscarded n).
Proof.
  apply _.
Qed.
#[global] Instance auth_natinf_min_ub_core_id n :
  CoreId (auth_natinf_min_ub n).
Proof.
  apply _.
Qed.

Lemma auth_natinf_min_auth_dfrac_op dq1 dq2 n :
  auth_natinf_min_auth (dq1 ⋅ dq2) n ≡ auth_natinf_min_auth dq1 n ⋅ auth_natinf_min_auth dq2 n.
Proof.
  rewrite /auth_natinf_min_auth auth_auth_dfrac_op.
  rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)) -core_id_dup (comm _ (◯ _)) //.
Qed.
#[global] Instance auth_natinf_min_auth_dfrac_is_op dq dq1 dq2 n :
  IsOp dq dq1 dq2 →
  IsOp' (auth_natinf_min_auth dq n) (auth_natinf_min_auth dq1 n) (auth_natinf_min_auth dq2 n).
Proof.
  rewrite /IsOp' /IsOp => ->. rewrite auth_natinf_min_auth_dfrac_op //.
Qed.

Lemma auth_natinf_min_ub_op n1 n2 :
  auth_natinf_min_ub (natinf.natinf_min n1 n2) = auth_natinf_min_ub n1 ⋅ auth_natinf_min_ub n2.
Proof.
  rewrite -auth_frag_op natinf_min_op_eq //.
Qed.
#[global] Instance auth_natinf_min_ub_is_op n n1 n2 :
  IsOp (Build_natinf_min n) (Build_natinf_min n1) (Build_natinf_min n2) →
  IsOp' (auth_natinf_min_ub n) (auth_natinf_min_ub n1) (auth_natinf_min_ub n2).
Proof.
  rewrite /IsOp' /IsOp /auth_natinf_min_ub => -> //.
Qed.

Lemma auth_natinf_min_auth_frag_op dq n :
  auth_natinf_min_auth dq n ≡ auth_natinf_min_auth dq n ⋅ auth_natinf_min_ub n.
Proof.
  rewrite -!assoc -auth_frag_op -core_id_dup //.
Qed.

Lemma auth_natinf_min_ub_op_le n n' :
  natinf_le n n' →
  auth_natinf_min_ub n = auth_natinf_min_ub n' ⋅ auth_natinf_min_ub n.
Proof.
  intros. rewrite -auth_natinf_min_ub_op natinf_min_r //.
Qed.

Lemma auth_natinf_min_auth_dfrac_valid dq n :
  ✓ auth_natinf_min_auth dq n ↔
  ✓ dq.
Proof.
  rewrite auth_both_dfrac_valid_discrete /=. naive_solver.
Qed.
Lemma auth_natinf_min_auth_valid n :
  ✓ auth_natinf_min_auth (DfracOwn 1) n.
Proof.
  apply auth_both_valid. done.
Qed.

Lemma auth_natinf_min_auth_dfrac_op_valid dq1 n1 dq2 n2 :
  ✓ (auth_natinf_min_auth dq1 n1 ⋅ auth_natinf_min_auth dq2 n2) ↔
  ✓ (dq1 ⋅ dq2) ∧ n1 = n2.
Proof.
  rewrite /auth_natinf_min_auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
  rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
  - move => /cmra_valid_op_l /auth_auth_dfrac_op_valid. naive_solver.
  - intros [? ->]. rewrite -core_id_dup -auth_auth_dfrac_op.
    apply auth_both_dfrac_valid_discrete. done.
Qed.
Lemma auth_natinf_min_auth_op_valid n1 n2 :
  ✓ (auth_natinf_min_auth (DfracOwn 1) n1 ⋅ auth_natinf_min_auth (DfracOwn 1) n2) ↔
  False.
Proof.
  rewrite auth_natinf_min_auth_dfrac_op_valid. naive_solver.
Qed.

Lemma auth_natinf_min_both_dfrac_valid dq n m :
  ✓ (auth_natinf_min_auth dq n ⋅ auth_natinf_min_ub m) ↔
  ✓ dq ∧ natinf_le n m.
Proof.
  rewrite -assoc -auth_frag_op auth_both_dfrac_valid_discrete.
  rewrite natinf_min_included natinf_min_op_eq /=. split.
  - intros (Hle_min & Hle & _). split; first done.
    destruct (total natinf_le n m); first done.
    rewrite natinf_min_r // in Hle.
  - intros []. split_and!; try done.
    rewrite natinf_min_l; done.
Qed.
Lemma auth_natinf_min_both_valid n m :
  ✓ (auth_natinf_min_auth (DfracOwn 1) n ⋅ auth_natinf_min_ub m) ↔
  natinf_le n m.
Proof.
  rewrite auth_natinf_min_both_dfrac_valid dfrac_valid_own. naive_solver.
Qed.

Lemma auth_natinf_min_ub_mono n1 n2 :
  natinf_le n2 n1 →
  auth_natinf_min_ub n1 ≼ auth_natinf_min_ub n2.
Proof.
  intros. apply auth_frag_mono, natinf_min_included. done.
Qed.

Lemma auth_natinf_min_included dq n :
  auth_natinf_min_ub n ≼ auth_natinf_min_auth dq n.
Proof.
  apply cmra_included_r.
Qed.

Lemma auth_natinf_min_auth_persist dq n :
  auth_natinf_min_auth dq n ~~> auth_natinf_min_auth DfracDiscarded n.
Proof.
  eapply cmra_update_op_proper; last done.
  eapply auth_update_auth_persist.
Qed.
Lemma auth_natinf_min_auth_update {n} n' :
  natinf_le n' n →
  auth_natinf_min_auth (DfracOwn 1) n ~~> auth_natinf_min_auth (DfracOwn 1) n'.
Proof.
  intros. apply auth_update, natinf_min_local_update. done.
Qed.

#[global] Opaque auth_natinf_min_auth.
#[global] Opaque auth_natinf_min_ub.
