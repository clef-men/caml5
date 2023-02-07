From iris.algebra Require Export
  dfrac.
From iris.proofmode Require Import
  proofmode.
From iris.bi.lib Require Import
  fractional.
From iris.base_logic.lib Require Export
  own.

From caml5 Require Import
  prelude.
From caml5.algebra Require Import
  auth_Z_max.

Class AuthZMaxG Σ := {
  auth_Z_max_G_inG : inG Σ auth_Z_max_R ;
}.
#[local] Existing Instance auth_Z_max_G_inG.

Definition auth_Z_max_Σ := #[
  GFunctor auth_Z_max_R
].
#[global] Instance subG_auth_Z_max_Σ Σ :
  subG auth_Z_max_Σ Σ →
  AuthZMaxG Σ.
Proof.
  solve_inG.
Qed.

Section auth_Z_max_G.
  Context `{!AuthZMaxG Σ}.
  Implicit Types n m p : Z.

  Definition auth_Z_max_auth γ dq n :=
    own γ (auth_Z_max_auth dq n).
  Definition auth_Z_max_frag γ n :=
    own γ (auth_Z_max_frag n).

  #[global] Instance auth_Z_max_auth_timeless γ dq n :
    Timeless (auth_Z_max_auth γ dq n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_Z_max_auth_persistent γ n :
    Persistent (auth_Z_max_auth γ DfracDiscarded n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_Z_max_frag_timeless γ n :
    Timeless (auth_Z_max_frag γ n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_Z_max_frag_persistent γ n :
    Persistent (auth_Z_max_frag γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_Z_max_auth_fractional γ n :
    Fractional (λ q, auth_Z_max_auth γ (DfracOwn q) n).
  Proof.
    intros ?*. rewrite -own_op -auth_Z_max_auth_dfrac_op //.
  Qed.
  #[global] Instance auth_Z_max_auth_as_fractional γ q n :
    AsFractional (auth_Z_max_auth γ (DfracOwn q) n) (λ q, auth_Z_max_auth γ (DfracOwn q) n) q.
  Proof.
    split; done || apply _.
  Qed.

  Lemma auth_Z_max_auth_persist γ dq n :
    auth_Z_max_auth γ dq n ==∗
    auth_Z_max_auth γ DfracDiscarded n.
  Proof.
    iApply own_update. apply auth_Z_max_auth_update_persist.
  Qed.

  Lemma auth_Z_max_alloc n :
    ⊢ |==> ∃ γ,
      auth_Z_max_auth γ (DfracOwn 1) n ∗ auth_Z_max_frag γ n.
  Proof.
    iMod (own_alloc (auth_Z_max.auth_Z_max_auth (DfracOwn 1) n ⋅ auth_Z_max.auth_Z_max_frag n)) as "(% & ? & ?)".
    { apply auth_Z_max_both_valid. done. }
    naive_solver.
  Qed.

  Lemma auth_Z_max_auth_valid γ dq a :
    auth_Z_max_auth γ dq a -∗
    ⌜✓ dq⌝.
  Proof.
    iIntros. iDestruct (own_valid with "[$]") as %?%auth_Z_max_auth_dfrac_valid. done.
  Qed.
  Lemma auth_Z_max_auth_valid_2 γ dq1 dq2 n1 n2 :
    auth_Z_max_auth γ dq1 n1 -∗
    auth_Z_max_auth γ dq2 n2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ n1 = n2⌝.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (own_valid_2 with "H●1 H●2") as %?%auth_Z_max_auth_dfrac_op_valid. done.
  Qed.
  Lemma auth_Z_max_auth_exclusive γ n1 n2 :
    auth_Z_max_auth γ (DfracOwn 1) n1 -∗
    auth_Z_max_auth γ (DfracOwn 1) n2 -∗
    False.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (auth_Z_max_auth_valid_2 with "H●1 H●2") as %(? & _). done.
  Qed.

  Lemma auth_Z_max_frag_get γ q n :
    auth_Z_max_auth γ q n -∗
    auth_Z_max_frag γ n.
  Proof.
    apply own_mono, auth_Z_max_included.
  Qed.
  Lemma auth_Z_max_frag_le {γ n} n' :
    (n' ≤ n)%Z →
    auth_Z_max_frag γ n -∗
    auth_Z_max_frag γ n'.
  Proof.
    intros. apply own_mono, auth_Z_max_frag_mono. done.
  Qed.

  Lemma auth_Z_max_both_valid γ dq n m :
    auth_Z_max_auth γ dq n -∗
    auth_Z_max_frag γ m -∗
    ⌜m ≤ n⌝%Z.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (own_valid_2 with "H●1 H●2") as %?%auth_Z_max_both_dfrac_valid.
    naive_solver.
  Qed.

  Lemma auth_Z_max_update {γ n} n' :
    (n ≤ n')%Z →
    auth_Z_max_auth γ (DfracOwn 1) n ==∗
    auth_Z_max_auth γ (DfracOwn 1) n'.
  Proof.
    iIntros "% H●".
    iMod (own_update with "H●"); first apply auth_Z_max_auth_update; done.
  Qed.
End auth_Z_max_G.

#[global] Typeclasses Opaque auth_Z_max_auth.
#[global] Typeclasses Opaque auth_Z_max_frag.
