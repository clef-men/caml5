From caml5 Require Import
  prelude.
From caml5.lang Require Export
  lang.
From caml5.lang Require Import
  notations
  proofmode.

Definition identifier := proph_id.
Canonical identifier_O := leibnizO identifier.
Implicit Types id : identifier.

Definition LitIdentifier id := LitProphecy id.
Coercion LitIdentifier : identifier >-> base_lit.

Notation NewId := NewProph
( only parsing
).

Section heapGS.
  Context `{!heapGS Σ}.

  Definition identifier_model id : iProp Σ :=
    ∃ prophs, proph id prophs.

  Lemma identifier_model_exclusive id :
    identifier_model id -∗
    identifier_model id -∗
    False.
  Proof.
    iIntros "(% & Hid1) (% & Hid2)". iApply (proph_exclusive with "Hid1 Hid2").
  Qed.

  Lemma wp_new_id E :
    {{{ True }}}
      NewId @ E
    {{{ id, RET #id; identifier_model id }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (wp_new_proph with "[//]"). iIntros "%prophs %p Hp".
    iApply "HΦ". iExists prophs. done.
  Qed.
End heapGS.

#[global] Opaque LitIdentifier.

#[global] Opaque identifier_model.
