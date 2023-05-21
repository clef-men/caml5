From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.
From caml5.std Require Import
  lst
  stack.

Section heapGS.
  Context `{!heapGS Σ}.
  Implicit Types l : loc.
  Implicit Types v t lst : val.

  Definition std_stack_make : val :=
    λ: <>,
      ref lst_nil.

  Definition std_stack_is_empty : val :=
    λ: "t",
      lst_is_empty !"t".

  Definition std_stack_push : val :=
    λ: "t" "v",
      "t" <- lst_cons "v" !"t".

  Definition std_stack_pop : val :=
    λ: "t",
      let: "lst" := !"t" in
      if: lst_is_empty "lst" then (
        NONE
      ) else (
        "t" <- lst_tail "lst" ;;
        SOME (lst_head "lst")
      ).

  Definition std_stack_model t vs : iProp Σ :=
    ∃ l lst, ⌜t = #l⌝ ∗ l ↦ lst ∗ lst_model lst vs.

  #[global] Instance std_stack_model_timeless t vs :
    Timeless (std_stack_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma std_stack_make_spec :
    {{{ True }}}
      std_stack_make #()
    {{{ t,
      RET t;
      std_stack_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec. wp_alloc l as "Hl".
    iApply "HΦ". iExists l, lst_nil. iFrame. iSplitL; first done. iApply lst_nil_spec.
  Qed.

  Lemma std_stack_is_empty_spec t vs :
    {{{
      std_stack_model t vs
    }}}
      std_stack_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      std_stack_model t vs
    }}}.
  Proof.
    iIntros "%Φ (%l & %lst & -> & Hl & #Hlst) HΦ".
    wp_rec. wp_load.
    wp_apply (lst_is_empty_spec with "Hlst"). iIntros "_".
    iApply "HΦ". iExists l, lst. naive_solver.
  Qed.

  Lemma std_stack_push_spec t vs v :
    {{{
      std_stack_model t vs
    }}}
      std_stack_push t v
    {{{
      RET #();
      std_stack_model t (v :: vs)
    }}}.
  Proof.
    iIntros "%Φ (%l & %lst & -> & Hl & #Hlst) HΦ".
    wp_rec. wp_load.
    wp_apply (lst_cons_spec with "Hlst"). iIntros "%lst' #Hlst'".
    wp_store.
    iApply "HΦ". iExists l, lst'. naive_solver.
  Qed.

  Lemma std_stack_pop_spec t vs :
    {{{
      std_stack_model t vs
    }}}
      std_stack_pop t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          std_stack_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          std_stack_model t vs'
      end
    }}}.
  Proof.
    iIntros "%Φ (%l & %lst & -> & Hl & #Hlst) HΦ".
    wp_rec. wp_load. wp_pures.
    wp_apply (lst_is_empty_spec with "Hlst"). iIntros "_".
    destruct vs as [| v vs]; wp_pures.
    - iApply ("HΦ" $! None). repeat iSplitR; try done.
      iExists l, lst. naive_solver.
    - wp_apply (lst_tail_spec with "Hlst"); first done. iIntros "%lst' #Hlst'".
      wp_store.
      wp_apply (lst_head_spec with "Hlst"); first done. iIntros "_".
      wp_pures.
      iApply ("HΦ" $! (Some v)). iExists vs. repeat iSplitR; try done.
      iExists l, lst'. naive_solver.
  Qed.

  Lemma std_stack_unboxed t vs :
    std_stack_model t vs -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "(%l & %lst & -> & Hl & #Hlst) //".
  Qed.

  Definition std_stack :=
    Build_stack true
      std_stack_make_spec
      std_stack_is_empty_spec
      std_stack_push_spec
      std_stack_pop_spec
      std_stack_unboxed.
End heapGS.

#[global] Opaque std_stack_make.
#[global] Opaque std_stack_is_empty.
#[global] Opaque std_stack_push.
#[global] Opaque std_stack_pop.

#[global] Opaque std_stack_model.
