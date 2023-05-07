From iris.proofmode Require Import
  proofmode.

From caml5 Require Import
  prelude.
From caml5.common Require Export
  natinf.
From caml5 Require Export
  base.
From caml5.algebra Require Import
  lib.auth_natinf_max.

Class AuthNatinfMaxG Σ := {
  auth_natinf_max_G_inG : inG Σ auth_natinf_max_R ;
}.
#[local] Existing Instance auth_natinf_max_G_inG.

Definition auth_natinf_max_Σ := #[
  GFunctor auth_natinf_max_R
].
#[global] Instance subG_auth_natinf_max_Σ Σ :
  subG auth_natinf_max_Σ Σ →
  AuthNatinfMaxG Σ.
Proof.
  solve_inG.
Qed.

Section auth_natinf_max_G.
  Context `{auth_natinf_max_G : !AuthNatinfMaxG Σ}.
  Implicit Types n m : natinf.

  Definition auth_natinf_max_auth γ dq n :=
    own γ (auth_natinf_max_auth dq n).
  Definition auth_natinf_max_lb γ n :=
    own γ (auth_natinf_max_lb n).

  #[global] Instance auth_natinf_max_auth_timeless γ dq n :
    Timeless (auth_natinf_max_auth γ dq n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_natinf_max_auth_persistent γ n :
    Persistent (auth_natinf_max_auth γ DfracDiscarded n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_natinf_max_lb_timeless γ n :
    Timeless (auth_natinf_max_lb γ n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_natinf_max_lb_persistent γ n :
    Persistent (auth_natinf_max_lb γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_natinf_max_auth_fractional γ n :
    Fractional (λ q, auth_natinf_max_auth γ (DfracOwn q) n).
  Proof.
    intros ?*. rewrite -own_op -auth_natinf_max_auth_dfrac_op //.
  Qed.
  #[global] Instance auth_natinf_max_auth_as_fractional γ q n :
    AsFractional (auth_natinf_max_auth γ (DfracOwn q) n) (λ q, auth_natinf_max_auth γ (DfracOwn q) n) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma auth_natinf_max_alloc n :
    ⊢ |==> ∃ γ,
      auth_natinf_max_auth γ (DfracOwn 1) n.
  Proof.
    iMod (own_alloc (auth_natinf_max.auth_natinf_max_auth (DfracOwn 1) n)) as "(% & ?)".
    { apply auth_natinf_max_auth_valid. }
    naive_solver.
  Qed.

  Lemma auth_natinf_max_auth_valid γ dq a :
    auth_natinf_max_auth γ dq a -∗
    ⌜✓ dq⌝.
  Proof.
    iIntros. iDestruct (own_valid with "[$]") as %?%auth_natinf_max_auth_dfrac_valid. done.
  Qed.
  Lemma auth_natinf_max_auth_combine γ dq1 n1 dq2 n2 :
    auth_natinf_max_auth γ dq1 n1 -∗
    auth_natinf_max_auth γ dq2 n2 -∗
      auth_natinf_max_auth γ (dq1 ⋅ dq2) n1 ∗
      ⌜n1 = n2⌝.
  Proof.
    iIntros "Hauth1 Hauth2". iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as %(? & <-)%auth_natinf_max_auth_dfrac_op_valid.
    rewrite -auth_natinf_max_auth_dfrac_op. naive_solver.
  Qed.
  Lemma auth_natinf_max_auth_valid_2 γ dq1 n1 dq2 n2 :
    auth_natinf_max_auth γ dq1 n1 -∗
    auth_natinf_max_auth γ dq2 n2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ n1 = n2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_natinf_max_auth_combine with "Hauth1 Hauth2") as "(Hauth & %)".
    iDestruct (auth_natinf_max_auth_valid with "Hauth") as %?.
    done.
  Qed.
  Lemma auth_natinf_max_auth_agree γ dq1 n1 dq2 n2 :
    auth_natinf_max_auth γ dq1 n1 -∗
    auth_natinf_max_auth γ dq2 n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_natinf_max_auth_valid_2 with "Hauth1 Hauth2") as %?. naive_solver.
  Qed.
  Lemma auth_natinf_max_auth_dfrac_ne γ1 dq1 n1 γ2 dq2 n2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    auth_natinf_max_auth γ1 dq1 n1 -∗
    auth_natinf_max_auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% Hauth1 Hauth2" (->).
    iDestruct (auth_natinf_max_auth_valid_2 with "Hauth1 Hauth2") as %?; naive_solver.
  Qed.
  Lemma auth_natinf_max_auth_ne γ1 n1 γ2 dq2 n2 :
    auth_natinf_max_auth γ1 (DfracOwn 1) n1 -∗
    auth_natinf_max_auth γ2 dq2 n2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    intros. iApply auth_natinf_max_auth_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma auth_natinf_max_auth_exclusive γ n1 n2 :
    auth_natinf_max_auth γ (DfracOwn 1) n1 -∗
    auth_natinf_max_auth γ (DfracOwn 1) n2 -∗
    False.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (auth_natinf_max_auth_valid_2 with "Hauth1 Hauth2") as %(? & _). done.
  Qed.
  Lemma auth_natinf_max_auth_persist γ dq n :
    auth_natinf_max_auth γ dq n ==∗
    auth_natinf_max_auth γ DfracDiscarded n.
  Proof.
    iApply own_update. apply auth_natinf_max_auth_persist.
  Qed.

  Lemma auth_natinf_max_lb_0 γ :
    ⊢ |==> auth_natinf_max_lb γ (natinf_nat 0).
  Proof.
    iApply own_unit.
  Qed.
  Lemma auth_natinf_max_lb_get γ q n :
    auth_natinf_max_auth γ q n -∗
    auth_natinf_max_lb γ n.
  Proof.
    apply own_mono, auth_natinf_max_included.
  Qed.
  Lemma auth_natinf_max_lb_le {γ n} n' :
    natinf_le n' n →
    auth_natinf_max_lb γ n -∗
    auth_natinf_max_lb γ n'.
  Proof.
    intros. apply own_mono, auth_natinf_max_lb_mono. done.
  Qed.

  Lemma auth_natinf_max_valid γ dq n m :
    auth_natinf_max_auth γ dq n -∗
    auth_natinf_max_lb γ m -∗
    ⌜natinf_le m n⌝.
  Proof.
    iIntros "Hauth1 Hauth2".
    iDestruct (own_valid_2 with "Hauth1 Hauth2") as %?%auth_natinf_max_both_dfrac_valid.
    naive_solver.
  Qed.

  Lemma auth_natinf_max_update {γ n} n' :
    natinf_le n n' →
    auth_natinf_max_auth γ (DfracOwn 1) n ==∗
    auth_natinf_max_auth γ (DfracOwn 1) n'.
  Proof.
    iIntros "% Hauth".
    iMod (own_update with "Hauth"); first apply auth_natinf_max_auth_update; done.
  Qed.
End auth_natinf_max_G.

#[global] Opaque auth_natinf_max_auth.
#[global] Opaque auth_natinf_max_lb.
