From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.
From caml5.std Require Import
  dlchain
  deque.

Section heapGS.
  Context `{!heapGS Σ}.

  Definition std_deque_make : val :=
    λ: <>,
      let: "t" := dlchain_singleton #() #() #() in
      dlchain_set_prev "t" "t" ;;
      dlchain_set_next "t" "t" ;;
      "t".

  Definition std_deque_is_empty : val :=
    λ: "t",
      dlchain_next "t" = "t".

  Definition std_deque_push_front : val :=
    λ: "t" "v",
      let: "old_front" := dlchain_next "t" in
      let: "front" := dlchain_singleton "t" "v" "old_front" in
      dlchain_set_next "t" "front" ;;
      dlchain_set_prev "old_front" "front".

  Definition std_deque_pop_front : val :=
    λ: "t",
      if: std_deque_is_empty "t" then (
        NONE
      ) else (
        let: "old_front" := dlchain_next "t" in
        let: "front" := dlchain_next "old_front" in
        dlchain_set_next "t" "front" ;;
        dlchain_set_prev "front" "t" ;;
        SOME (dlchain_data "old_front")
      ).

  Definition std_deque_push_back : val :=
    λ: "t" "v",
      let: "old_back" := dlchain_prev "t" in
      let: "back" := dlchain_singleton "old_back" "v" "t" in
      dlchain_set_next "old_back" "back" ;;
      dlchain_set_prev "t" "back".

  Definition std_deque_pop_back : val :=
    λ: "t",
      if: std_deque_is_empty "t" then (
        NONE
      ) else (
        let: "old_back" := dlchain_prev "t" in
        let: "back" := dlchain_prev "old_back" in
        dlchain_set_next "old_back" "back" ;;
        dlchain_set_prev "t" "back" ;;
        SOME (dlchain_data "old_back")
      ).

  Definition std_deque_model t vs : iProp Σ :=
    ∃ back, dlchain_model t (DfracOwn 1) back (#() :: vs) back t.

  #[global] Instance std_deque_model_timeless t vs :
    Timeless (std_deque_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma std_deque_make_spec :
    {{{ True }}}
      std_deque_make #()
    {{{ t,
      RET t;
      std_deque_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (dlchain_singleton_spec with "[//]"). iIntros "%sent Hsent".
    wp_pures.
    wp_apply (dlchain_set_prev_spec with "Hsent"); first (simpl; lia). iIntros "Hsent".
    wp_pures.
    wp_apply (dlchain_set_next_spec with "Hsent"). iIntros "%_ (Hsent & _)".
    wp_pures.
    iApply "HΦ". iExists sent. auto with iFrame.
  Qed.

  Lemma std_deque_is_empty_spec t vs :
    {{{
      std_deque_model t vs
    }}}
      std_deque_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      std_deque_model t vs
    }}}.
  Proof.
    iIntros "%Φ (%back & Hsent) HΦ".
    wp_rec.
    wp_apply (dlchain_next_spec with "Hsent"). iIntros "%front (Hsent & Hfront)".
    iDestruct (dlchain_unboxed with "Hsent") as %Hunboxed. wp_pures. clear Hunboxed.
    destruct vs as [| v vs].
    - iDestruct (dlchain_model_nil_2 with "Hfront") as %(-> & ->).
      rewrite /= bool_decide_eq_true_2; last done.
      iApply "HΦ". iExists back. auto with iFrame.
    - iAssert ⌜t ≠ front⌝%I as %?; first admit.
      rewrite /= bool_decide_eq_false_2; last done.
      iDestruct (dlchain_model_app_1 with "Hsent Hfront") as "Hsent".
      iApply "HΦ". iExists back. auto with iFrame.
  Admitted.

  Lemma std_deque_push_front_spec t vs v :
    {{{
      std_deque_model t vs
    }}}
      std_deque_push_front t v
    {{{
      RET #();
      std_deque_model t (v :: vs)
    }}}.
  Proof.
  Admitted.

  Lemma std_deque_pop_front_spec t vs :
    {{{
      std_deque_model t vs
    }}}
      std_deque_pop_front t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          std_deque_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          std_deque_model t vs'
      end
    }}}.
  Proof.
  Admitted.

  Lemma std_deque_push_back_spec t vs v :
    {{{
      std_deque_model t vs
    }}}
      std_deque_push_back t v
    {{{
      RET #();
      std_deque_model t (vs ++ [v])
    }}}.
  Proof.
  Admitted.

  Lemma std_deque_pop_back_spec t vs :
    {{{
      std_deque_model t vs
    }}}
      std_deque_pop_back t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          std_deque_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          std_deque_model t vs'
      end
    }}}.
  Proof.
  Admitted.

  Lemma std_deque_unboxed t vs :
    std_deque_model t vs -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "(%back & Hsent)". iApply (dlchain_unboxed with "Hsent").
  Qed.

  Definition std_deque :=
    Build_deque true
      std_deque_make_spec
      std_deque_is_empty_spec
      std_deque_push_front_spec
      std_deque_pop_front_spec
      std_deque_push_back_spec
      std_deque_pop_back_spec
      std_deque_unboxed.
End heapGS.

#[global] Opaque std_deque_make.
#[global] Opaque std_deque_is_empty.
#[global] Opaque std_deque_push_front.
#[global] Opaque std_deque_pop_front.
#[global] Opaque std_deque_push_back.
#[global] Opaque std_deque_pop_back.

#[global] Opaque std_deque_model.
