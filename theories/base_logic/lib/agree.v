From iris.algebra Require Import
  agree.
From iris.proofmode Require Import
  proofmode.

From caml5 Require Import
  prelude.
From caml5 Require Export
  base.

Class AgreeG Σ A := {
  agree_G_inG : inG Σ (agreeR A) ;
}.
#[local] Existing Instance agree_G_inG.

Definition agree_Σ A := #[
  GFunctor (agreeR A)
].
#[global] Instance subG_agree_Σ A Σ :
  subG (agree_Σ A) Σ →
  AgreeG Σ A.
Proof.
  solve_inG.
Qed.

Section agree_G.
  Context `{!AgreeG Σ A}.

  Definition agree_on γ a :=
    own γ (to_agree a).

  #[global] Instance agree_on_timeless γ a :
    Discrete a →
    Timeless (agree_on γ a).
  Proof.
    apply _.
  Qed.
  #[global] Instance agree_on_persistent γ a :
    Persistent (agree_on γ a).
  Proof.
    apply _.
  Qed.

  Lemma agree_alloc a :
    ⊢ |==> ∃ γ,
      agree_on γ a.
  Proof.
    apply own_alloc. done.
  Qed.

  Section cmra_discrete.
    Context `{!OfeDiscrete A}.

    Lemma agree_on_agree γ a1 a2 :
      agree_on γ a1 -∗
      agree_on γ a2 -∗
      ⌜a1 ≡ a2⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (own_valid_2 with "H1 H2") as %?%to_agree_op_valid. done.
    Qed.
    Lemma agree_on_agree_L `{!LeibnizEquiv A} γ a1 a2 :
      agree_on γ a1 -∗
      agree_on γ a2 -∗
      ⌜a1 = a2⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (agree_on_agree with "H1 H2") as %?%leibniz_equiv. done.
    Qed.
  End cmra_discrete.
End agree_G.

#[global] Opaque agree_on.
