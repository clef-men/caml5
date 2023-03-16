From iris.proofmode Require Import
  proofmode.

From caml5 Require Import
  prelude.
From caml5 Require Export
  base.
From caml5.algebra Require Import
  auth_excl.

Class AuthExclG Σ A := {
  auth_excl_G_inG : inG Σ (auth_excl_R A) ;
}.
#[local] Existing Instance auth_excl_G_inG.

Definition auth_excl_Σ A := #[
  GFunctor (auth_excl_R A)
].
#[global] Instance subG_auth_excl_Σ A Σ :
  subG (auth_excl_Σ A) Σ →
  AuthExclG Σ A.
Proof.
  solve_inG.
Qed.

Section auth_excl_G.
  Context `{!AuthExclG Σ A}.
  Implicit Types a b : A.

  Definition auth_excl_auth γ dq a :=
    own γ (●E{dq} a).
  Definition auth_excl_frag γ a :=
    own γ (◯E a).

  #[global] Instance auth_excl_auth_timeless γ dq a :
    Discrete a →
    Timeless (auth_excl_auth γ dq a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_excl_auth_persistent γ a :
    Persistent (auth_excl_auth γ DfracDiscarded a).
  Proof.
    apply _.
  Qed.
  #[global] Instance auth_excl_frag_timeless γ a :
    Discrete a →
    Timeless (auth_excl_frag γ a).
  Proof.
    apply _.
  Qed.

  #[global] Instance auth_excl_auth_fractional γ a :
    Fractional (λ q, auth_excl_auth γ (DfracOwn q) a).
  Proof.
    intros ?*. rewrite -own_op -auth_excl_auth_dfrac_op //.
  Qed.
  #[global] Instance auth_excl_auth_as_fractional γ q a :
    AsFractional (auth_excl_auth γ (DfracOwn q) a) (λ q, auth_excl_auth γ (DfracOwn q) a) q.
  Proof.
    split; done || apply _.
  Qed.

  Lemma auth_excl_auth_persist γ dq a :
    auth_excl_auth γ dq a ==∗
    auth_excl_auth γ DfracDiscarded a.
  Proof.
    iApply own_update. apply auth_excl_auth_update_persist.
  Qed.

  Lemma auth_excl_alloc a b :
    a ≡ b →
    ⊢ |==> ∃ γ,
      auth_excl_auth γ (DfracOwn 1) a ∗ auth_excl_frag γ b.
  Proof.
    iIntros.
    iMod (own_alloc (●E a ⋅ ◯E b)) as "(% & ? & ?)"; first by apply auth_excl_both_valid.
    iExists _. iFrame. done.
  Qed.
  Lemma auth_excl_alloc' a :
    ⊢ |==> ∃ γ,
      auth_excl_auth γ (DfracOwn 1) a ∗ auth_excl_frag γ a.
  Proof.
    iApply auth_excl_alloc. done.
  Qed.

  Lemma auth_excl_update {γ a b} a' b' :
    a' ≡ b' →
    auth_excl_auth γ (DfracOwn 1) a -∗
    auth_excl_frag γ b ==∗
      auth_excl_auth γ (DfracOwn 1) a' ∗
      auth_excl_frag γ b'.
  Proof.
    iIntros "% H● H◯".
    iMod (own_update_2 with "H● H◯") as "(? & ?)"; first by apply auth_excl_both_update.
    iFrame. done.
  Qed.
  Lemma auth_excl_update' {γ a b} a' :
    auth_excl_auth γ (DfracOwn 1) a -∗
    auth_excl_frag γ b ==∗
      auth_excl_auth γ (DfracOwn 1) a' ∗
      auth_excl_frag γ a'.
  Proof.
    iApply auth_excl_update. done.
  Qed.

  Section cmra_discrete.
    Context `{!OfeDiscrete A}.

    Lemma auth_excl_auth_valid γ dq a :
      auth_excl_auth γ dq a -∗
      ⌜✓ dq⌝.
    Proof.
      iIntros. iDestruct (own_valid with "[$]") as %?%auth_excl_auth_dfrac_valid. done.
    Qed.
    Lemma auth_excl_auth_combine γ dq1 a1 dq2 a2 :
      auth_excl_auth γ dq1 a1 -∗
      auth_excl_auth γ dq2 a2 -∗
        auth_excl_auth γ (dq1 ⋅ dq2) a1 ∗
        ⌜a1 ≡ a2⌝.
    Proof.
      iIntros "H●1 H●2". iCombine "H●1 H●2" as "H●".
      iDestruct (own_valid with "H●") as %(? & Heq)%auth_excl_auth_dfrac_op_valid.
      iEval (rewrite -Heq -auth_excl_auth_dfrac_op) in "H●".
      naive_solver.
    Qed.
    Lemma auth_excl_auth_combine_L `{!LeibnizEquiv A} γ dq1 a1 dq2 a2 :
      auth_excl_auth γ dq1 a1 -∗
      auth_excl_auth γ dq2 a2 -∗
        auth_excl_auth γ (dq1 ⋅ dq2) a1 ∗
        ⌜a1 = a2⌝.
    Proof.
      iIntros "H●1 H●2".
      iDestruct (auth_excl_auth_combine with "H●1 H●2") as "($ & %)". naive_solver.
    Qed.
    Lemma auth_excl_auth_valid_2 γ dq1 a1 dq2 a2 :
      auth_excl_auth γ dq1 a1 -∗
      auth_excl_auth γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ a1 ≡ a2⌝.
    Proof.
      iIntros "H●1 H●2".
      iDestruct (auth_excl_auth_combine with "H●1 H●2") as "(H● & %)".
      iDestruct (auth_excl_auth_valid with "H●") as %?.
      done.
    Qed.
    Lemma auth_excl_auth_valid_2_L `{!LeibnizEquiv A} γ dq1 a1 dq2 a2 :
      auth_excl_auth γ dq1 a1 -∗
      auth_excl_auth γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2) ∧ a1 = a2⌝.
    Proof.
      iIntros "H●1 H●2".
      iDestruct (auth_excl_auth_valid_2 with "H●1 H●2") as %?. naive_solver.
    Qed.
    Lemma auth_excl_auth_agree γ dq1 a1 dq2 a2 :
      auth_excl_auth γ dq1 a1 -∗
      auth_excl_auth γ dq2 a2 -∗
      ⌜a1 ≡ a2⌝.
    Proof.
      iIntros "H●1 H●2".
      iDestruct (auth_excl_auth_valid_2 with "H●1 H●2") as %?. naive_solver.
    Qed.
    Lemma auth_excl_auth_agree_L `{!LeibnizEquiv A} γ dq1 a1 dq2 a2 :
      auth_excl_auth γ dq1 a1 -∗
      auth_excl_auth γ dq2 a2 -∗
      ⌜a1 = a2⌝.
    Proof.
      iIntros "H●1 H●2".
      iDestruct (auth_excl_auth_agree with "H●1 H●2") as %?. naive_solver.
    Qed.
    Lemma auth_excl_auth_exclusive γ a1 a2 :
      auth_excl_auth γ (DfracOwn 1) a1 -∗
      auth_excl_auth γ (DfracOwn 1) a2 -∗
      False.
    Proof.
      iIntros "H●1 H●2".
      iDestruct (auth_excl_auth_valid_2 with "H●1 H●2") as %(? & _). done.
    Qed.

    Lemma auth_excl_frag_exclusive γ a1 a2 :
      auth_excl_frag γ a1 -∗
      auth_excl_frag γ a1 -∗
      False.
    Proof.
      iIntros "H◯1 H◯2".
      iDestruct (own_valid_2 with "H◯1 H◯2") as %[]%auth_excl_frag_op_valid.
    Qed.

    Lemma auth_excl_both_agree γ dq a b :
      auth_excl_auth γ dq a -∗
      auth_excl_frag γ b -∗
      ⌜a ≡ b⌝.
    Proof.
      iIntros "H● H◯".
      iDestruct (own_valid_2 with "H● H◯") as %?%auth_excl_both_dfrac_valid.
      naive_solver.
    Qed.
    Lemma auth_excl_both_agree_L `{!LeibnizEquiv A} γ dq a b :
      auth_excl_auth γ dq a -∗
      auth_excl_frag γ b -∗
      ⌜a = b⌝.
    Proof.
      iIntros "H● H◯".
      iDestruct (auth_excl_both_agree with "H● H◯") as %?. naive_solver.
    Qed.
  End cmra_discrete.
End auth_excl_G.

#[global] Opaque auth_excl_auth.
#[global] Opaque auth_excl_frag.
