From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.

Implicit Types t : val.

Record random `{!heapGS Σ} {unboxed : bool} := {
  random_make : val ;
  random_gen : val ;

  random_inv : val → iProp Σ ;

  random_inv_persistent t :
    Persistent (random_inv t) ;

  random_make_spec :
    {{{ True }}}
      random_make #()
    {{{ t, RET t; random_inv t }}} ;

  random_gen_spec t (bound : Z) :
    (0 < bound)%Z →
    {{{ random_inv t }}}
      random_gen t #bound
    {{{ n, RET #n; ⌜0 ≤ n < bound⌝%Z }}} ;

  random_unboxed :
    if unboxed then ∀ t,
      random_inv t -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments random _ {_} _ : assert.
#[global] Arguments Build_random {_ _} _ {_ _ _ _} _ _ _ : assert.
#[global] Existing Instance random_inv_persistent.

Section random.
  Context `{!heapGS Σ} {unboxed} (random : random Σ unboxed).

  Definition random_gen_Z : val :=
    λ: "t" "lb" "ub",
      "lb" + random.(random_gen) "t" ("ub" - "lb").
  Definition random_gen_nat :=
    random_gen_Z.
  Definition random_gen_bool : val :=
    λ: "t",
      random.(random_gen) "t" #2.

  Lemma random_gen_Z_spec t lb ub :
    (lb < ub)%Z →
    {{{ random.(random_inv) t }}}
      random_gen_Z t #lb #ub
    {{{ n, RET #n; ⌜lb ≤ n < ub⌝%Z }}}.
  Proof.
    iIntros "%Hlt %Φ Hinv HΦ".
    wp_rec. wp_pures.
    wp_apply (random_gen_spec with "Hinv"); first lia. iIntros "%n %Hn".
    wp_pures.
    iApply "HΦ". iPureIntro. lia.
  Qed.
  Lemma random_gen_nat_spec t lb ub :
    lb < ub →
    {{{ random.(random_inv) t }}}
      random_gen_nat t #lb #ub
    {{{ n, RET #n; ⌜lb ≤ n < ub⌝ }}}.
  Proof.
    iIntros "%Hlt %Φ Hinv HΦ".
    wp_rec. wp_pures.
    wp_apply (random_gen_spec with "Hinv"); first lia. iIntros "%n %Hn".
    wp_pures.
    destruct (Z_of_nat_complete n) as (m & ->); first lia.
    assert ((lb + m)%Z = lb + m) as -> by lia.
    iApply "HΦ". iPureIntro. lia.
  Qed.
  Lemma random_gen_bool_spec t :
    {{{ random.(random_inv) t }}}
      random_gen_bool t
    {{{ b, RET #(bool_to_Z b); True }}}.
  Proof.
    iIntros "%Φ Hinv HΦ".
    wp_rec. wp_pures.
    wp_apply (random_gen_spec with "Hinv"); first done. iIntros "%n %Hn".
    assert (∃ (b : bool), n = bool_to_Z b) as (b & ->).
    { assert (n = 0 ∨ n = 1) as [-> | ->] by lia; [exists false | exists true]; done. }
    iApply "HΦ". done.
  Qed.
End random.

#[global] Opaque random_gen_Z.
#[global] Opaque random_gen_nat.
#[global] Opaque random_gen_bool.
