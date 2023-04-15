From iris.proofmode Require Import
  proofmode.

From caml5 Require Import
  prelude.
From caml5.common Require Export
  natinf.
From caml5 Require Export
  base.
From caml5.algebra Require Import
  lib.auth_natinf_min.

Class AuthNatinfMinG Σ := {
  auth_natinf_min_G_inG : inG Σ auth_natinf_min_R ;
}.
#[local] Existing Instance auth_natinf_min_G_inG.

Definition auth_natinf_min_Σ := #[
  GFunctor auth_natinf_min_R
].
#[global] Instance subG_auth_natinf_min_Σ Σ :
  subG auth_natinf_min_Σ Σ →
  AuthNatinfMinG Σ.
Proof.
  solve_inG.
Qed.

Section auth_natinf_min_G.
  Context `{auth_natinf_min_G : !AuthNatinfMinG Σ}.
  Implicit Types n m : natinf.

  Definition auth_natinf_min_auth γ dq n :=
    own γ (auth_natinf_min_auth dq n).
  Definition auth_natinf_min_frag γ n :=
    own γ (auth_natinf_min_frag n).

  #[global] Instance auth_natinf_min_auth_timeless γ dq n :
    Timeless (auth_natinf_min_auth γ dq n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_natinf_min_auth_persistent γ n :
    Persistent (auth_natinf_min_auth γ DfracDiscarded n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_natinf_min_frag_timeless γ n :
    Timeless (auth_natinf_min_frag γ n).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_natinf_min_frag_persistent γ n :
    Persistent (auth_natinf_min_frag γ n).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_natinf_min_auth_fractional γ n :
    Fractional (λ q, auth_natinf_min_auth γ (DfracOwn q) n).
  Proof.
    intros ?*. rewrite -own_op -auth_natinf_min_auth_dfrac_op //.
  Qed.
  #[global] Instance auth_natinf_min_auth_as_fractional γ q n :
    AsFractional (auth_natinf_min_auth γ (DfracOwn q) n) (λ q, auth_natinf_min_auth γ (DfracOwn q) n) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma auth_natinf_min_alloc n :
    ⊢ |==> ∃ γ,
      auth_natinf_min_auth γ (DfracOwn 1) n.
  Proof.
    iMod (own_alloc (auth_natinf_min.auth_natinf_min_auth (DfracOwn 1) n)) as "(% & ?)".
    { apply auth_natinf_min_auth_valid. }
    naive_solver.
  Qed.

  Lemma auth_natinf_min_auth_valid γ dq a :
    auth_natinf_min_auth γ dq a -∗
    ⌜✓ dq⌝.
  Proof.
    iIntros. iDestruct (own_valid with "[$]") as %?%auth_natinf_min_auth_dfrac_valid. done.
  Qed.
  Lemma auth_natinf_min_auth_combine γ dq1 n1 dq2 n2 :
    auth_natinf_min_auth γ dq1 n1 -∗
    auth_natinf_min_auth γ dq2 n2 -∗
      auth_natinf_min_auth γ (dq1 ⋅ dq2) n1 ∗
      ⌜n1 = n2⌝.
  Proof.
    iIntros "H●1 H●2". iCombine "H●1 H●2" as "H●".
    iDestruct (own_valid with "H●") as %(? & <-)%auth_natinf_min_auth_dfrac_op_valid.
    rewrite -auth_natinf_min_auth_dfrac_op. naive_solver.
  Qed.
  Lemma auth_natinf_min_auth_valid_2 γ dq1 n1 dq2 n2 :
    auth_natinf_min_auth γ dq1 n1 -∗
    auth_natinf_min_auth γ dq2 n2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ n1 = n2⌝.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (auth_natinf_min_auth_combine with "H●1 H●2") as "(H● & %)".
    iDestruct (auth_natinf_min_auth_valid with "H●") as %?.
    done.
  Qed.
  Lemma auth_natinf_min_auth_agree γ dq1 n1 dq2 n2 :
    auth_natinf_min_auth γ dq1 n1 -∗
    auth_natinf_min_auth γ dq2 n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (auth_natinf_min_auth_valid_2 with "H●1 H●2") as %?. naive_solver.
  Qed.
  Lemma auth_natinf_min_auth_exclusive γ n1 n2 :
    auth_natinf_min_auth γ (DfracOwn 1) n1 -∗
    auth_natinf_min_auth γ (DfracOwn 1) n2 -∗
    False.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (auth_natinf_min_auth_valid_2 with "H●1 H●2") as %(? & _). done.
  Qed.

  Lemma auth_natinf_min_frag_inf γ :
    ⊢ |==> auth_natinf_min_frag γ natinf_inf.
  Proof.
    iApply own_unit.
  Qed.
  Lemma auth_natinf_min_frag_get γ q n :
    auth_natinf_min_auth γ q n -∗
    auth_natinf_min_frag γ n.
  Proof.
    apply own_mono, auth_natinf_min_included.
  Qed.
  Lemma auth_natinf_min_frag_le {γ n} n' :
    natinf_le n n' →
    auth_natinf_min_frag γ n -∗
    auth_natinf_min_frag γ n'.
  Proof.
    intros. apply own_mono, auth_natinf_min_frag_mono. done.
  Qed.

  Lemma auth_natinf_min_valid γ dq n m :
    auth_natinf_min_auth γ dq n -∗
    auth_natinf_min_frag γ m -∗
    ⌜natinf_le n m⌝.
  Proof.
    iIntros "H●1 H●2".
    iDestruct (own_valid_2 with "H●1 H●2") as %?%auth_natinf_min_both_dfrac_valid.
    naive_solver.
  Qed.

  Lemma auth_natinf_min_auth_persist γ dq n :
    auth_natinf_min_auth γ dq n ==∗
    auth_natinf_min_auth γ DfracDiscarded n.
  Proof.
    iApply own_update. apply auth_natinf_min_auth_persist.
  Qed.

  Lemma auth_natinf_min_update {γ n} n' :
    natinf_le n' n →
    auth_natinf_min_auth γ (DfracOwn 1) n ==∗
    auth_natinf_min_auth γ (DfracOwn 1) n'.
  Proof.
    iIntros "% H●".
    iMod (own_update with "H●"); first apply auth_natinf_min_auth_update; done.
  Qed.
End auth_natinf_min_G.

#[global] Opaque auth_natinf_min_auth.
#[global] Opaque auth_natinf_min_frag.
