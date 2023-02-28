From iris.algebra Require Import
  excl.
From iris.proofmode Require Import
  proofmode.

From caml5 Require Import
  prelude.
From caml5 Require Export
  base.

Class ExclG Σ A := {
  excl_G_inG : inG Σ (exclR A) ;
}.
#[local] Existing Instance excl_G_inG.

Definition excl_Σ A := #[
  GFunctor (exclR A)
].
#[global] Instance subG_excl_Σ A Σ :
  subG (excl_Σ A) Σ →
  ExclG Σ A.
Proof.
  solve_inG.
Qed.

Section excl_G.
  Context `{!ExclG Σ A}.
  Implicit Types a b : A.

  Definition excl γ a :=
    own γ (Excl a).

  #[global] Instance excl_timeless γ a :
    Discrete a →
    Timeless (excl γ a).
  Proof.
    apply _.
  Qed.

  Lemma excl_alloc a :
    ⊢ |==> ∃ γ, excl γ a.
  Proof.
    apply own_alloc. done.
  Qed.

  Lemma excl_update γ a b :
    excl γ a ==∗
    excl γ b.
  Proof.
    apply own_update, cmra_update_exclusive. done.
  Qed.

  Lemma excl_exclusive `{!OfeDiscrete A} γ a1 a2 :
    excl γ a1 -∗
    excl γ a2 -∗
    False.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %[].
  Qed.
End excl_G.

#[global] Opaque excl.
