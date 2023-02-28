From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.
From caml5.std Require Import
  lst.

Record fun_queue `{!heapGS Σ} := {
  fun_queue_make : val ;
  fun_queue_is_empty : val ;
  fun_queue_push : val ;
  fun_queue_pop : val ;

  fun_queue_model : val → list val → iProp Σ ;

  fun_queue_model_persistent t vs :
    Persistent (fun_queue_model t vs) ;
  fun_queue_model_timeless t vs :
    Timeless (fun_queue_model t vs) ;

  fun_queue_make_spec :
    {{{ True }}}
      fun_queue_make #()
    {{{ t, RET t; fun_queue_model t [] }}} ;

  fun_queue_is_empty_spec t vs :
    {{{ fun_queue_model t vs }}}
      fun_queue_is_empty t
    {{{ RET #(bool_decide (vs = [])); True }}} ;

  fun_queue_push_spec t vs v :
    {{{ fun_queue_model t vs }}}
      fun_queue_push t v
    {{{ t', RET t'; fun_queue_model t' (v :: vs) }}} ;

  fun_queue_pop_spec t vs :
    {{{ fun_queue_model t vs }}}
      fun_queue_pop t
    {{{ w,
      RET w;
      (⌜vs = [] ∧ w = NONEV⌝) ∨
      (∃ vs' v t', ⌜vs = vs' ++ [v] ∧ w = SOMEV (v, t')⌝ ∗ fun_queue_model t' vs')
    }}} ;
}.
#[global] Arguments fun_queue _ {_} : assert.
#[global] Arguments Build_fun_queue {_ _ _ _ _ _ _ _ _} _ _ _ _ : assert.
#[global] Existing Instance fun_queue_model_persistent.
#[global] Existing Instance fun_queue_model_timeless.

Section std_fun_queue.
  Context `{!heapGS Σ}.
  Implicit Types v t back front : val.

  Notation "t '.(back)'" := (Fst t)
  ( at level 5
  ) : expr_scope.
  Notation "t '.(front)'" := (Snd t)
  ( at level 5
  ) : expr_scope.

  Definition std_fun_queue_make : val :=
    λ: <>,
      (lst_nil, lst_nil).

  Definition std_fun_queue_is_empty : val :=
    λ: "t",
      lst_is_empty "t".(front) && lst_is_empty "t".(back).

  Definition std_fun_queue_push : val :=
    λ: "t" "v",
      (lst_cons "v" "t".(back), "t".(front)).

  Definition std_fun_queue_pop : val :=
    λ: "t",
      if: lst_is_empty "t".(front) then (
        let: "front" := lst_rev "t".(back) in
        if: lst_is_empty "front" then (
          NONE
        ) else (
          SOME (lst_head "front", (lst_nil, lst_tail "front"))
        )
      ) else (
        SOME (lst_head "t".(front), ("t".(back), lst_tail "t".(front)))
      ).

  Definition std_fun_queue_model t vs : iProp Σ :=
    ∃ back vs_back front vs_front,
    ⌜t = (back, front)%V ∧ vs = vs_back ++ reverse vs_front⌝ ∗
    lst_model back vs_back ∗ lst_model front vs_front.

  #[global] Instance std_fun_queue_model_persistent t vs :
    Persistent (std_fun_queue_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance std_fun_queue_model_timeless t vs :
    Timeless (std_fun_queue_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma std_fun_queue_make_spec :
    {{{ True }}}
      std_fun_queue_make #()
    {{{ t, RET t; std_fun_queue_model t [] }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec. wp_pures.
    iModIntro. iApply "HΦ". iExists lst_nil, [], lst_nil, []. list_simplifier.
    iSplit; first done. iDestruct lst_nil_spec as "$".
  Qed.

  Lemma std_fun_queue_is_empty_spec t vs :
    {{{ std_fun_queue_model t vs }}}
      std_fun_queue_is_empty t
    {{{ RET #(bool_decide (vs = [])); True }}}.
  Proof.
    iIntros "%Φ (%back & %vs_back & %front & %vs_front & (-> & ->) & #Hback & #Hfront) HΦ".
    wp_rec. wp_pures.
    wp_apply (lst_is_empty_spec with "Hfront"). iIntros "_".
    destruct vs_front as [| v_front vs_front]; wp_pures.
    - wp_apply (lst_is_empty_spec with "Hback"). iIntros "_".
      destruct vs_back as [| v_back vs_back]; list_simplifier; iApply ("HΦ" with "[//]").
    - rewrite bool_decide_eq_false_2; last first.
      { rewrite reverse_cons. intros (_ & (_ & [=])%app_eq_nil)%app_eq_nil. }
      iApply ("HΦ" with "[//]").
  Qed.

  Lemma std_fun_queue_push_spec t vs v :
    {{{ std_fun_queue_model t vs }}}
      std_fun_queue_push t v
    {{{ t', RET t'; std_fun_queue_model t' (v :: vs) }}}.
  Proof.
    iIntros "%Φ (%back & %vs_back & %front & %vs_front & (-> & ->) & #Hback & #Hfront) HΦ".
    wp_rec. wp_pures.
    wp_apply (lst_cons_spec with "Hback"). iIntros "%back' #Hback'".
    wp_pures.
    iApply "HΦ". iExists back', (v :: vs_back), front, vs_front. auto with iFrame.
  Qed.

  Lemma std_fun_queue_pop_spec t vs :
    {{{ std_fun_queue_model t vs }}}
      std_fun_queue_pop t
    {{{ w,
      RET w;
      (⌜vs = [] ∧ w = NONEV⌝) ∨
      (∃ vs' v t', ⌜vs = vs' ++ [v] ∧ w = SOMEV (v, t')⌝ ∗ std_fun_queue_model t' vs')
    }}}.
  Proof.
    iIntros "%Φ (%back & %vs_back & %front & %vs_front & (-> & ->) & #Hback & #Hfront) HΦ".
    wp_rec. wp_pures.
    wp_apply (lst_is_empty_spec with "Hfront"). iIntros "_".
    destruct vs_front as [| v_front vs_front]; wp_pures.
    - iClear "Hfront". clear.
      wp_apply (lst_rev_spec with "Hback"). iIntros "%front #Hfront".
      wp_pures.
      wp_apply (lst_is_empty_spec with "Hfront"). iIntros "_".
      destruct (reverse vs_back) as [| v vs_front] eqn:Heq;
        apply (f_equal reverse) in Heq; rewrite reverse_involutive in Heq; subst;
        wp_pures.
      + iApply "HΦ". iLeft. done.
      + wp_apply (lst_tail_spec with "Hfront"); first done. iIntros "%front' #Hfront'".
        wp_pures.
        wp_apply (lst_head_spec with "Hfront"); first done. iIntros "_".
        wp_pures.
        iModIntro. iApply "HΦ". iRight. iExists (reverse vs_front), v, _. iSplit.
        { iPureIntro. split; last done.
          rewrite reverse_nil reverse_cons. list_simplifier. done.
        }
        iExists lst_nil, [], front', vs_front. repeat iSplit; try done. iApply lst_nil_spec.
    - wp_apply (lst_tail_spec with "Hfront"); first done. iIntros "%front' Hfront'".
      wp_pures.
      wp_apply (lst_head_spec with "Hfront"); first done. iIntros "_".
      wp_pures.
      iModIntro. iApply "HΦ". iRight. iExists (vs_back ++ reverse vs_front), v_front, _. iSplit.
      { iPureIntro. split; last done. list_simplifier. rewrite reverse_cons //. }
      iExists back, vs_back, front', vs_front. auto with iFrame.
  Qed.

  Definition std_fun_queue : fun_queue Σ :=
    Build_fun_queue
      std_fun_queue_make_spec
      std_fun_queue_is_empty_spec
      std_fun_queue_push_spec
      std_fun_queue_pop_spec.
End std_fun_queue.

#[global] Opaque std_fun_queue_make.
#[global] Opaque std_fun_queue_is_empty.
#[global] Opaque std_fun_queue_push.
#[global] Opaque std_fun_queue_pop.

#[global] Opaque std_fun_queue_model.
