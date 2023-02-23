From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.
From caml5.std Require Import
  chain.

Record queue `{!heapGS Σ} := {
  queue_make : val ;
  queue_is_empty : val ;
  queue_push : val ;
  queue_pop : val ;

  queue_model : val → list val → iProp Σ ;

  queue_model_timeless t vs :
    Timeless (queue_model t vs) ;

  queue_make_spec :
    {{{ True }}}
      queue_make #()
    {{{ t, RET t; queue_model t [] }}} ;

  queue_is_empty_spec t vs :
    {{{ queue_model t vs }}}
      queue_is_empty t
    {{{ RET #(bool_decide (vs = [])); queue_model t vs }}} ;

  queue_push_spec t vs v :
    {{{ queue_model t vs }}}
      queue_push t v
    {{{ RET #(); queue_model t (v :: vs) }}} ;

  queue_pop_spec t vs :
    {{{ queue_model t vs }}}
      queue_pop t
    {{{ w,
      RET w;
      (⌜vs = [] ∧ w = NONEV⌝ ∗ queue_model t []) ∨
      (∃ vs' v, ⌜vs = vs' ++ [v] ∧ w = SOMEV v⌝ ∗ queue_model t vs')
    }}} ;
}.
#[global] Arguments queue _ {_} : assert.
#[global] Arguments Build_queue {_ _ _ _ _ _ _ _} _ _ _ _ : assert.
#[global] Existing Instance queue_model_timeless.

Section std_queue.
  Context `{!heapGS Σ}.
  Implicit Types l : loc.
  Implicit Types t v hd tl : val.

  Notation queue_offset_head := 0%Z.
  Notation queue_offset_tail := 1%Z.

  Notation "t '.(head)'" := (t +ₗ queue_offset_head)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(tail)'" := (t +ₗ queue_offset_tail)%stdpp
  ( at level 5
  ) : stdpp_scope.
  Notation "t '.(head)'" := (t +ₗ #queue_offset_head)%E
  ( at level 5
  ) : expr_scope.
  Notation "t '.(tail)'" := (t +ₗ #queue_offset_tail)%E
  ( at level 5
  ) : expr_scope.

  Definition std_queue_make : val :=
    λ: <>,
      let: "tl" := chain_cons #() #() in
      AllocN #2 "tl".

  Definition std_queue_is_empty : val :=
    λ: "t",
      !"t".(head) = !"t".(tail).

  Definition std_queue_push : val :=
    λ: "t" "v",
      let: "tl" := chain_cons #() #() in
      chain_set_head !"t".(tail) "v" ;;
      chain_set_tail !"t".(tail) "tl" ;;
      "t".(tail) <- "tl".

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
    ∃ l hd tl,
    ⌜t = #l⌝ ∗
    l.(head) ↦ hd ∗ l.(tail) ↦ tl ∗
    chain_model hd (DfracOwn 1) (reverse vs) tl ∗ chain_model tl (DfracOwn 1) [ #()] #().

  #[global] Instance std_queue_model_timeless t vs :
    Timeless (std_queue_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma std_queue_make_spec :
    {{{ True }}}
      std_queue_make #()
    {{{ t, RET t; std_queue_model t [] }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (chain_cons_spec _ (DfracOwn 1)); [done | by iApply chain_model_nil |]. iIntros "%tl Htl_model".
    wp_pures. wp_alloc l as "Hl"; first done.
    iDestruct (array_cons with "Hl") as "(Hhd & Htl)".
    iEval (setoid_rewrite <- loc_add_0) in "Hhd".
    iDestruct (array_singleton with "Htl") as "Htl".
    iModIntro. iApply "HΦ". iExists l, tl, tl. iFrame. iSplit; [done | by iApply chain_model_nil].
  Qed.

  Lemma std_queue_is_empty_spec t vs :
    {{{ std_queue_model t vs }}}
      std_queue_is_empty t
    {{{ RET #(bool_decide (vs = [])); std_queue_model t vs }}}.
  Proof.
    iIntros "%Φ (%l & %hd & %tl & -> & Hhd & Htl & Hhd_model & Htl_model) HΦ".
    wp_rec. wp_pures. wp_load. wp_pures. wp_load.
    destruct vs as [| v vs].
    - iDestruct (chain_model_nil with "Hhd_model") as %->.
      iDestruct (chain_model_unboxed with "Htl_model") as %?.
      wp_pures.
      iEval (rewrite bool_decide_eq_true_2). iApply "HΦ". iExists l, tl, tl. auto with iFrame.
    - iDestruct (chain_model_unboxed with "Htl_model") as %?.
      wp_pures.
      iDestruct (chain_model_ne with "Htl_model Hhd_model") as %?; first (rewrite reverse_length /=; lia).
      rewrite (bool_decide_eq_false_2 (hd = tl)); last done.
      iApply "HΦ". iExists l, hd, tl. auto with iFrame.
  Qed.

  Lemma std_queue_push_spec t vs v :
    {{{ std_queue_model t vs }}}
      std_queue_push t v
    {{{ RET #(); std_queue_model t (v :: vs) }}}.
  Proof.
    iIntros "%Φ (%l & %hd & %tl & -> & Hhd & Htl & Hhd_model & Htl_model) HΦ".
    wp_rec. wp_pures.
    wp_apply (chain_cons_spec _ (DfracOwn 1)); [done | by iApply chain_model_nil |]. iIntros "%tl' Htl'_model".
    wp_pures. wp_load.
    wp_apply (chain_set_head_spec with "Htl_model"). iIntros "Htl_model".
    wp_pures. wp_load.
    wp_apply (chain_set_tail_spec with "Htl_model"). iIntros "%_ (Htl_model & _)".
    iDestruct (chain_model_app_1 with "Hhd_model Htl_model") as "Hhd_model".
    rewrite -reverse_cons.
    wp_pures. wp_store.
    iModIntro. iApply "HΦ". iExists l, hd, tl'. auto with iFrame.
  Qed.

  Lemma std_queue_pop_spec t vs :
    {{{ std_queue_model t vs }}}
      std_queue_pop t
    {{{ w,
      RET w;
      (⌜vs = [] ∧ w = NONEV⌝ ∗ std_queue_model t []) ∨
      (∃ vs' v, ⌜vs = vs' ++ [v] ∧ w = SOMEV v⌝ ∗ std_queue_model t vs')
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_apply (std_queue_is_empty_spec with "Hmodel"). iIntros "(%l & %hd & %tl & -> & Hhd & Htl & Hhd_model & Htl_model)".
    destruct (reverse vs) as [| v rev_vs] eqn:Heq;
      apply (f_equal reverse) in Heq; rewrite reverse_involutive in Heq; subst;
      wp_pures.
    { iModIntro. iApply "HΦ". iLeft. iSplit; first done. iExists l, hd, tl. auto with iFrame. }
    rewrite reverse_cons bool_decide_eq_false_2; last eauto using app_cons_not_nil.
    wp_pures. wp_load.
    wp_apply (chain_head_spec with "Hhd_model"). iIntros "Hhd_model".
    wp_pures. wp_load.
    wp_apply (chain_tail_spec with "Hhd_model"). iIntros "%hd' (Hhd_model & Hhd'_model)".
    wp_store. wp_pures.
    iModIntro. iApply "HΦ". iRight. iExists (reverse rev_vs), v. iSplit; first done.
    iExists l, hd', tl. rewrite reverse_involutive. auto with iFrame.
  Qed.

  Definition std_queue : queue Σ :=
    Build_queue
      std_queue_make_spec
      std_queue_is_empty_spec
      std_queue_push_spec
      std_queue_pop_spec.
End std_queue.

#[global] Opaque std_queue_make.
#[global] Opaque std_queue_is_empty.
#[global] Opaque std_queue_push.
#[global] Opaque std_queue_pop.

#[global] Typeclasses Opaque std_queue_model.
