From iris.algebra Require Import
  proofmode_classes.

From caml5 Require Import
  prelude.
From caml5.algebra Require Export
  base.
From caml5.algebra Require Import
  auth_option
  Z_min.

Implicit Types n m p : Z.

Definition auth_Z_min :=
  auth_option Z_min_R.
Definition auth_Z_min_R :=
  auth_option_R Z_min_R.
Definition auth_Z_min_UR :=
  auth_option_UR Z_min_R.

Definition auth_Z_min_auth dq n : auth_Z_min_UR :=
  ●O{dq} Build_Z_min n ⋅ ◯O Build_Z_min n.
Definition auth_Z_min_frag n : auth_Z_min_UR :=
  ◯O Build_Z_min n.

#[global] Instance auth_Z_min_cmra_discrete :
  CmraDiscrete auth_Z_min_R.
Proof.
  apply _.
Qed.

#[global] Instance auth_Z_min_auth_core_id n :
  CoreId (auth_Z_min_auth DfracDiscarded n).
Proof.
  apply _.
Qed.
#[global] Instance auth_Z_min_frag_core_id n :
  CoreId (auth_Z_min_frag n).
Proof.
  apply _.
Qed.

Lemma auth_Z_min_auth_dfrac_op dq1 dq2 n :
  auth_Z_min_auth (dq1 ⋅ dq2) n ≡ auth_Z_min_auth dq1 n ⋅ auth_Z_min_auth dq2 n.
Proof.
  rewrite /auth_Z_min_auth auth_option_auth_dfrac_op.
  rewrite (comm _ (●O{dq2} _)) -!assoc (assoc _ (◯O _)) -core_id_dup (comm _ (◯O _)) //.
Qed.
#[global] Instance auth_Z_min_auth_dfrac_is_op dq dq1 dq2 n :
  IsOp dq dq1 dq2 →
  IsOp' (auth_Z_min_auth dq n) (auth_Z_min_auth dq1 n) (auth_Z_min_auth dq2 n).
Proof.
  rewrite /IsOp' /IsOp => ->. rewrite auth_Z_min_auth_dfrac_op //.
Qed.

Lemma auth_Z_min_frag_op n1 n2 :
  auth_Z_min_frag (n1 `min` n2) = auth_Z_min_frag n1 ⋅ auth_Z_min_frag n2.
Proof.
  rewrite -auth_option_frag_op Z_min_op_eq //.
Qed.
#[global] Instance auth_Z_min_frag_is_op n n1 n2 :
  IsOp (Build_Z_min n) (Build_Z_min n1) (Build_Z_min n2) →
  IsOp' (auth_Z_min_frag n) (auth_Z_min_frag n1) (auth_Z_min_frag n2).
Proof.
  rewrite /IsOp' /IsOp /auth_Z_min_frag => -> //.
Qed.

Lemma auth_Z_min_auth_frag_op dq n :
  auth_Z_min_auth dq n ≡ auth_Z_min_auth dq n ⋅ auth_Z_min_frag n.
Proof.
  rewrite -!assoc -auth_option_frag_op -core_id_dup //.
Qed.

Lemma auth_Z_min_frag_op_le n n' :
  (n ≤ n')%Z →
  auth_Z_min_frag n = auth_Z_min_frag n' ⋅ auth_Z_min_frag n.
Proof.
  intros. rewrite -auth_Z_min_frag_op Z.min_r //.
Qed.

Lemma auth_Z_min_auth_dfrac_valid dq n :
  ✓ auth_Z_min_auth dq n ↔
  ✓ dq.
Proof.
  rewrite auth_option_both_dfrac_valid_discrete /=. naive_solver.
Qed.
Lemma auth_Z_min_auth_valid n :
  ✓ auth_Z_min_auth (DfracOwn 1) n.
Proof.
  rewrite auth_Z_min_auth_dfrac_valid //.
Qed.

Lemma auth_Z_min_auth_dfrac_op_valid dq1 n1 dq2 n2 :
  ✓ (auth_Z_min_auth dq1 n1 ⋅ auth_Z_min_auth dq2 n2) ↔
  ✓ (dq1 ⋅ dq2) ∧ n1 = n2.
Proof.
  rewrite /auth_Z_min_auth (comm _ (●O{dq2} _)) -!assoc (assoc _ (◯O _)).
  rewrite -auth_option_frag_op (comm _ (◯O _)) assoc. split.
  - move => /cmra_valid_op_l /auth_option_auth_dfrac_op_valid. naive_solver.
  - intros [? ->]. rewrite -core_id_dup -auth_option_auth_dfrac_op.
    apply auth_option_both_dfrac_valid_discrete. naive_solver.
Qed.
Lemma auth_Z_min_auth_op_valid n1 n2 :
  ✓ (auth_Z_min_auth (DfracOwn 1) n1 ⋅ auth_Z_min_auth (DfracOwn 1) n2) ↔
  False.
Proof.
  rewrite auth_Z_min_auth_dfrac_op_valid. naive_solver.
Qed.

Lemma auth_Z_min_both_dfrac_valid dq n m :
  ✓ (auth_Z_min_auth dq n ⋅ auth_Z_min_frag m) ↔
  ✓ dq ∧ (n ≤ m)%Z.
Proof.
  rewrite -assoc -auth_option_frag_op auth_option_both_dfrac_valid_discrete.
  rewrite Z_min_included Z_min_op_eq /=. naive_solver lia.
Qed.
Lemma auth_Z_min_both_valid n m :
  ✓ (auth_Z_min_auth (DfracOwn 1) n ⋅ auth_Z_min_frag m) ↔
  (n ≤ m)%Z.
Proof.
  rewrite auth_Z_min_both_dfrac_valid dfrac_valid_own. naive_solver.
Qed.

Lemma auth_Z_min_frag_mono n1 n2 :
  (n2 ≤ n1)%Z →
  auth_Z_min_frag n1 ≼ auth_Z_min_frag n2.
Proof.
  intros. apply auth_option_frag_mono, Z_min_included. done.
Qed.

Lemma auth_Z_min_included dq n :
  auth_Z_min_frag n ≼ auth_Z_min_auth dq n.
Proof.
  apply cmra_included_r.
Qed.

Lemma auth_Z_min_auth_persist dq n :
  auth_Z_min_auth dq n ~~> auth_Z_min_auth DfracDiscarded n.
Proof.
  eapply cmra_update_op_proper; last done.
  eapply auth_option_auth_persist.
Qed.
Lemma auth_Z_min_auth_update {n} n' :
  (n' ≤ n)%Z →
  auth_Z_min_auth (DfracOwn 1) n ~~> auth_Z_min_auth (DfracOwn 1) n'.
Proof.
  intros. apply auth_option_both_update, Z_min_local_update. done.
Qed.

#[global] Opaque auth_Z_min_auth.
#[global] Opaque auth_Z_min_frag.
