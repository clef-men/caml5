From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.
From caml5.std Require Import
  chain
  queue.

Section heapGS.
  Context `{!heapGS Σ}.
  Implicit Types l : loc.
  Implicit Types t v hd sent : val.

  Notation queue_offset_head := 0%Z.
  Notation queue_offset_sentinel := 1%Z.

  Notation "t '.(head)'" := (t +ₗ queue_offset_head)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(sentinel)'" := (t +ₗ queue_offset_sentinel)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(head)'" := (t +ₗ #queue_offset_head)%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(sentinel)'" := (t +ₗ #queue_offset_sentinel)%E
  ( at level 5
  ) : expr_scope.

  Definition std_queue_make : val :=
    λ: <>,
      let: "sent" := chain_cons #() #() in
      AllocN #2 "sent".

  Definition std_queue_is_empty : val :=
    λ: "t",
      !"t".(head) = !"t".(sentinel).

  Definition std_queue_push : val :=
    λ: "t" "v",
      let: "sent" := chain_cons #() #() in
      chain_set_head !"t".(sentinel) "v" ;;
      chain_set_tail !"t".(sentinel) "sent" ;;
      "t".(sentinel) <- "sent".

  Definition std_queue_pop : val :=
    λ: "t",
      if: std_queue_is_empty "t" then (
        NONE
      ) else (
        let: "v" := chain_head !"t".(head) in
        "t".(head) <- chain_tail !"t".(head) ;;
        SOME "v"
      ).

  Definition std_queue_model t vs : iProp Σ :=
    ∃ l hd sent,
    ⌜t = #l⌝ ∗
    l.(head) ↦ hd ∗ l.(sentinel) ↦ sent ∗
    chain_model hd (DfracOwn 1) (reverse vs) sent ∗ chain_model sent (DfracOwn 1) [ #()] #().

  #[global] Instance std_queue_model_timeless t vs :
    Timeless (std_queue_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma std_queue_make_spec :
    {{{ True }}}
      std_queue_make #()
    {{{ t,
      RET t;
      std_queue_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (chain_cons_spec _ (DfracOwn 1)); [done | by iApply chain_model_nil |]. iIntros "%sent Hsent_model".
    wp_pures. wp_alloc l as "Hl"; first done.
    iDestruct (array_cons with "Hl") as "(Hhd & Hsent)".
    iEval (setoid_rewrite <- loc_add_0) in "Hhd".
    iDestruct (array_singleton with "Hsent") as "Hsent".
    iModIntro. iApply "HΦ". iExists l, sent, sent. iFrame. iSplit; [done | by iApply chain_model_nil].
  Qed.

  Lemma std_queue_is_empty_spec t vs :
    {{{
      std_queue_model t vs
    }}}
      std_queue_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      std_queue_model t vs
    }}}.
  Proof.
    iIntros "%Φ (%l & %hd & %sent & -> & Hhd & Hsent & Hhd_model & Hsent_model) HΦ".
    wp_rec. wp_pures. wp_load. wp_pures. wp_load.
    destruct vs as [| v vs].
    - iDestruct (chain_model_nil with "Hhd_model") as %->.
      iDestruct (chain_unboxed with "Hsent_model") as %?.
      wp_pures.
      iEval (rewrite bool_decide_eq_true_2). iApply "HΦ". iExists l, sent, sent. auto with iFrame.
    - iDestruct (chain_unboxed with "Hsent_model") as %?.
      wp_pures.
      iDestruct (chain_model_ne with "Hsent_model Hhd_model") as %?; first (rewrite reverse_length /=; lia).
      rewrite (bool_decide_eq_false_2 (hd = sent)); last done.
      iApply "HΦ". iExists l, hd, sent. auto with iFrame.
  Qed.

  Lemma std_queue_push_spec t vs v :
    {{{
      std_queue_model t vs
    }}}
      std_queue_push t v
    {{{
      RET #();
      std_queue_model t (v :: vs)
    }}}.
  Proof.
    iIntros "%Φ (%l & %hd & %sent & -> & Hhd & Hsent & Hhd_model & Hsent_model) HΦ".
    wp_rec. wp_pures.
    wp_apply (chain_cons_spec _ (DfracOwn 1)); [done | by iApply chain_model_nil |]. iIntros "%sent' Hsent'_model".
    wp_pures. wp_load.
    wp_apply (chain_set_head_spec with "Hsent_model"). iIntros "Hsent_model".
    wp_pures. wp_load.
    wp_apply (chain_set_tail_spec with "Hsent_model"). iIntros "%_ (Hsent_model & _)".
    iDestruct (chain_model_app_1 with "Hhd_model Hsent_model") as "Hhd_model".
    rewrite -reverse_cons.
    wp_pures. wp_store.
    iModIntro. iApply "HΦ". iExists l, hd, sent'. auto with iFrame.
  Qed.

  Lemma std_queue_pop_spec t vs :
    {{{
      std_queue_model t vs
    }}}
      std_queue_pop t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          std_queue_model t []
      | Some v =>
          ∃ vs', ⌜vs = vs' ++ [v]⌝ ∗
          std_queue_model t vs'
      end
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_apply (std_queue_is_empty_spec with "Hmodel"). iIntros "(%l & %hd & %sent & -> & Hhd & Hsent & Hhd_model & Hsent_model)".
    destruct (reverse vs) as [| v rev_vs] eqn:Heq;
      apply (f_equal reverse) in Heq; rewrite reverse_involutive in Heq; subst;
      wp_pures.
    { iModIntro. iApply ("HΦ" $! None). iSplit; first done. iExists l, hd, sent. auto with iFrame. }
    rewrite reverse_cons bool_decide_eq_false_2; last eauto using app_cons_not_nil.
    wp_pures. wp_load.
    wp_apply (chain_head_spec with "Hhd_model"). iIntros "Hhd_model".
    wp_pures. wp_load.
    wp_apply (chain_tail_spec with "Hhd_model"). iIntros "%hd' (Hhd_model & Hhd'_model)".
    wp_store. wp_pures.
    iModIntro. iApply ("HΦ" $! (Some v)). iExists (reverse rev_vs). iSplit; first done.
    iExists l, hd', sent. rewrite reverse_involutive. auto with iFrame.
  Qed.

  Lemma std_queue_unboxed t vs :
    std_queue_model t vs -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "(%l & %hd & %sent & -> & Hhd & Hsent & Hhd_model & Hsent_model) //".
  Qed.

  Definition std_queue :=
    Build_queue true
      std_queue_make_spec
      std_queue_is_empty_spec
      std_queue_push_spec
      std_queue_pop_spec
      std_queue_unboxed.
End heapGS.

#[global] Opaque std_queue_make.
#[global] Opaque std_queue_is_empty.
#[global] Opaque std_queue_push.
#[global] Opaque std_queue_pop.

#[global] Opaque std_queue_model.
