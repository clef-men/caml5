From iris.algebra Require Import
  auth.
From iris.algebra Require Export
  dfrac
  updates.

From caml5 Require Import
  prelude.
From caml5.algebra Require Import
  nat_max.

Implicit Types n m p : nat.

Definition auth_nat_max :=
  auth nat_max_UR.
Definition auth_nat_max_R :=
  authR nat_max_UR.
Definition auth_nat_max_UR :=
  authUR nat_max_UR.

Definition auth_nat_max_auth dq n : auth_nat_max_UR :=
  ●{dq} Build_nat_max n ⋅ ◯ Build_nat_max n.
Definition auth_nat_max_frag n : auth_nat_max_UR :=
  ◯ Build_nat_max n.

#[global] Instance auth_nat_max_auth_core_id n :
  CoreId (auth_nat_max_auth DfracDiscarded n).
Proof.
  apply _.
Qed.
#[global] Instance auth_nat_max_frag_core_id n :
  CoreId (auth_nat_max_frag n).
Proof.
  apply _.
Qed.

Lemma auth_nat_max_auth_dfrac_op dq1 dq2 n :
  auth_nat_max_auth (dq1 ⋅ dq2) n ≡ auth_nat_max_auth dq1 n ⋅ auth_nat_max_auth dq2 n.
Proof.
  rewrite /auth_nat_max_auth auth_auth_dfrac_op.
  rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
  rewrite -core_id_dup (comm _ (◯ _)) //.
Qed.
Lemma auth_nat_max_frag_op n1 n2 :
  auth_nat_max_frag (n1 `max` n2) = auth_nat_max_frag n1 ⋅ auth_nat_max_frag n2.
Proof.
  rewrite -auth_frag_op nat_max_op_eq //.
Qed.
Lemma auth_nat_max_auth_frag_op dq n :
  auth_nat_max_auth dq n ≡ auth_nat_max_auth dq n ⋅ auth_nat_max_frag n.
Proof.
  rewrite /auth_nat_max_auth /auth_nat_max_frag.
  rewrite -!assoc -auth_frag_op nat_max_op_eq.
  rewrite Nat.max_id //.
Qed.

#[global] Instance auth_nat_max_auth_dfrac_is_op dq dq1 dq2 n :
  IsOp dq dq1 dq2 →
  IsOp' (auth_nat_max_auth dq n) (auth_nat_max_auth dq1 n) (auth_nat_max_auth dq2 n).
Proof.
  rewrite /IsOp' /IsOp => ->. rewrite auth_nat_max_auth_dfrac_op //.
Qed.
#[global] Instance auth_nat_max_frag_is_op n n1 n2 :
  IsOp (Build_nat_max n) (Build_nat_max n1) (Build_nat_max n2) →
  IsOp' (auth_nat_max_frag n) (auth_nat_max_frag n1) (auth_nat_max_frag n2).
Proof.
  rewrite /IsOp' /IsOp /auth_nat_max_frag => ->. done.
Qed.

Lemma auth_nat_max_frag_op_le n n' :
  n' ≤ n →
  auth_nat_max_frag n = auth_nat_max_frag n' ⋅ auth_nat_max_frag n.
Proof.
  intros. rewrite -auth_nat_max_frag_op Nat.max_r //.
Qed.

Lemma auth_nat_max_auth_dfrac_valid dq n :
  ✓ auth_nat_max_auth dq n ↔
  ✓ dq.
Proof.
  rewrite /auth_nat_max_auth auth_both_dfrac_valid_discrete /=. naive_solver.
Qed.
Lemma auth_nat_max_auth_valid n :
  ✓ auth_nat_max_auth (DfracOwn 1) n.
Proof.
  apply auth_both_valid. done.
Qed.

Lemma auth_nat_max_auth_dfrac_op_valid dq1 n1 dq2 n2 :
  ✓ (auth_nat_max_auth dq1 n1 ⋅ auth_nat_max_auth dq2 n2) ↔
  ✓ (dq1 ⋅ dq2) ∧ n1 = n2.
Proof.
  rewrite /auth_nat_max_auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
  rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
  - move => /cmra_valid_op_l /auth_auth_dfrac_op_valid. naive_solver.
  - intros [? ->]. rewrite -core_id_dup -auth_auth_dfrac_op.
    apply auth_both_dfrac_valid_discrete. done.
Qed.
Lemma auth_nat_max_auth_op_valid n1 n2 :
  ✓ (auth_nat_max_auth (DfracOwn 1) n1 ⋅ auth_nat_max_auth (DfracOwn 1) n2) ↔
  False.
Proof.
  rewrite auth_nat_max_auth_dfrac_op_valid. naive_solver.
Qed.

Lemma auth_nat_max_both_dfrac_valid dq n m :
  ✓ (auth_nat_max_auth dq n ⋅ auth_nat_max_frag m) ↔
  ✓ dq ∧ m ≤ n.
Proof.
  rewrite /auth_nat_max_auth /auth_nat_max_frag -assoc -auth_frag_op.
  rewrite auth_both_dfrac_valid_discrete nat_max_included /=.
  naive_solver lia.
Qed.
Lemma auth_nat_max_both_valid n m :
  ✓ (auth_nat_max_auth (DfracOwn 1) n ⋅ auth_nat_max_frag m) ↔
  m ≤ n.
Proof.
  rewrite auth_nat_max_both_dfrac_valid dfrac_valid_own. naive_solver.
Qed.

Lemma auth_nat_max_frag_mono n1 n2 :
  n1 ≤ n2 →
  auth_nat_max_frag n1 ≼ auth_nat_max_frag n2.
Proof.
  intros. apply auth_frag_mono, nat_max_included. done.
Qed.

Lemma auth_nat_max_included dq n :
  auth_nat_max_frag n ≼ auth_nat_max_auth dq n.
Proof.
  apply cmra_included_r.
Qed.

Lemma auth_nat_max_auth_update_persist dq n :
  auth_nat_max_auth dq n ~~> auth_nat_max_auth DfracDiscarded n.
Proof.
  intros. rewrite /auth_nat_max_auth /auth_nat_max_frag.
  eapply cmra_update_op_proper; last done.
  eapply auth_update_auth_persist.
Qed.
Lemma auth_nat_max_auth_update {n} n' :
  n ≤ n' →
  auth_nat_max_auth (DfracOwn 1) n ~~> auth_nat_max_auth (DfracOwn 1) n'.
Proof.
  intros. rewrite /auth_nat_max_auth /auth_nat_max_frag.
  apply auth_update, nat_max_local_update. done.
Qed.

#[global] Opaque auth_nat_max_auth.
#[global] Opaque auth_nat_max_frag.
