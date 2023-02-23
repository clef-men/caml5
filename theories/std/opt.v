From caml5 Require Import
  prelude.
From caml5.common Require Import
  tactics.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.

Section heapGS.
  Context `{!heapGS Σ}.
  Implicit Types b : bool.
  Implicit Types v t fn : val.
  Implicit Types o : option val.

  Definition opt_some : val :=
    λ: "v",
      SOME "v".
  Definition opt_none : val :=
    λ: <>,
      NONEV.

  Definition opt_is_some : val :=
    λ: "t",
      match: "t" with
        SOME <> => #true
      | NONE => #false
      end.
  Definition opt_is_none : val :=
    λ: "t",
      match: "t" with
        SOME <> => #false
      | NONE => #true
      end.

  Definition opt_value : val :=
    λ: "t" "default",
      match: "t" with
        SOME "v" => "v"
      | NONE => "default"
      end.
  Definition opt_get : val :=
    λ: "t",
      match: "t" with
        SOME "v" => "v"
      | NONE => Fail
      end.

  Definition opt_bind : val :=
    λ: "t" "fn",
      match: "t" with
        SOME "v" => "fn" "v"
      | NONE => NONEV
      end.
  Definition opt_map : val :=
    λ: "t" "fn",
      match: "t" with
        SOME "v" => SOME ("fn" "v")
      | NONE => NONEV
      end.
  Definition opt_iter : val :=
    λ: "t" "fn",
      match: "t" with
        SOME "v" => "fn" "v" ;; #()
      | NONE => #()
      end.

  Inductive opt_model' : val → option val → Prop :=
    | opt_model'_some v :
        opt_model' (SOMEV v) (Some v)
    | opt_model'_none :
        opt_model' NONEV None.
  #[local] Hint Constructors opt_model' : core.

  Definition opt_model t o : iProp Σ :=
    ⌜opt_model' t o⌝.

  #[global] Instance opt_model_persistent t o :
    Persistent (opt_model t o).
  Proof.
    apply _.
  Qed.
  #[global] Instance opt_model_timeless t o :
    Timeless (opt_model t o).
  Proof.
    apply _.
  Qed.

  Lemma opt_some_spec v :
    {{{ True }}}
      opt_some v
    {{{ t, RET t; opt_model t (Some v) }}}.
  Proof.
    iIntros "%Φ _ HΦ". wp_rec. wp_pures. iApply "HΦ". done.
  Qed.
  Lemma opt_none_spec :
    {{{ True }}}
      opt_none #()
    {{{ t, RET t; opt_model t None }}}.
  Proof.
    iIntros "%Φ _ HΦ". wp_rec. iApply "HΦ". done.
  Qed.

  Lemma opt_is_some_spec t o :
    {{{ opt_model t o }}}
      opt_is_some t
    {{{ RET #(bool_decide (is_Some o)); True }}}.
  Proof.
    iIntros "%Φ" ([]) "HΦ"; wp_rec; wp_pures; iApply "HΦ"; done.
  Qed.
  Lemma opt_is_none_spec t o :
    {{{ opt_model t o }}}
      opt_is_none t
    {{{ RET #(bool_decide (o = None)); True }}}.
  Proof.
    iIntros "%Φ" ([]) "HΦ"; wp_rec; wp_pures; iApply "HΦ"; done.
  Qed.

  Lemma opt_value_spec t o default :
    {{{ opt_model t o }}}
      opt_value t default
    {{{ RET if o is Some x then x else default; True }}}.
  Proof.
    iIntros "%Φ" ([]) "HΦ"; wp_rec; wp_pures; iApply "HΦ"; done.
  Qed.
  Lemma opt_get_spec t o v :
    {{{ opt_model t (Some v) }}}
      opt_get t
    {{{ RET v; True }}}.
  Proof.
    iIntros "%Φ %Ht HΦ". invert Ht.
    wp_rec. wp_pures. iApply "HΦ". done.
  Qed.

  Lemma opt_bind_spec t o fn Φ :
    {{{ opt_model t o ∗ ∀ v, WP fn v {{ t', ∃ o', opt_model t' o' ∗ Φ v o' }} }}}
      opt_bind t fn
    {{{ t', RET t';
      match o with
      | Some v => ∃ o', opt_model t' o' ∗ Φ v o'
      | None => opt_model t' None
      end
    }}}.
  Proof.
    iIntros "%Ψ (%Ht & Hfn) HΨ". invert Ht; wp_rec; wp_pures.
    - wp_apply (wp_wand with "Hfn"). iIntros "%t' (%o' & Ht' & HΦ)".
      iApply "HΨ". auto.
    - iApply "HΨ". done.
  Qed.
  Lemma opt_map_spec t o fn Φ :
    {{{ opt_model t o ∗ ∀ v, WP fn v {{ Φ }} }}}
      opt_map t fn
    {{{ t', RET t';
      match o with
      | Some v => ∃ v', opt_model t' (Some v') ∗ Φ v'
      | None => opt_model t' None
      end
    }}}.
  Proof.
    iIntros "%Ψ (%Ht & Hfn) HΨ". invert Ht; wp_rec; wp_pures.
    - wp_apply (wp_wand with "Hfn"). iIntros "%v' HΦ".
      wp_pures.
      iApply "HΨ". auto.
    - iApply "HΨ". done.
  Qed.
  Lemma opt_iter_spec t o fn P :
    {{{ opt_model t o ∗ ∀ v, WP fn v {{ _, P }} }}}
      opt_iter t fn
    {{{ RET #(); if o is Some v then P else True }}}.
  Proof.
    iIntros "%Φ (%Ht & Hfn) HΦ". invert Ht; wp_rec; wp_pures.
    - wp_apply (wp_wand with "Hfn"). iIntros "% HP".
      wp_pures.
      iApply "HΦ". done.
    - iApply "HΦ". done.
  Qed.
End heapGS.

#[global] Opaque opt_some.
#[global] Opaque opt_none.
#[global] Opaque opt_is_some.
#[global] Opaque opt_is_none.
#[global] Opaque opt_value.
#[global] Opaque opt_get.
#[global] Opaque opt_bind.
#[global] Opaque opt_map.
#[global] Opaque opt_iter.

#[global] Typeclasses Opaque opt_model.
