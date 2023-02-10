From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.
From caml5.std Require Import
  lst.

Record stack `{!heapGS Σ} := {
  stack_make : val ;
  stack_is_empty : val ;
  stack_push : val ;
  stack_pop : val ;

  stack_model : val → list val → iProp Σ ;

  stack_model_timeless t vs :
    Timeless (stack_model t vs) ;

  stack_make_spec :
    {{{ True }}}
      stack_make #()
    {{{ t, RET t; stack_model t [] }}} ;

  stack_is_empty_spec t vs :
    {{{ stack_model t vs }}}
      stack_is_empty t
    {{{ RET #(bool_decide (vs = [])); stack_model t vs }}} ;

  stack_push_spec t vs v :
    {{{ stack_model t vs }}}
      stack_push t v
    {{{ RET #(); stack_model t (v :: vs) }}} ;

  stack_pop_spec t vs :
    {{{ stack_model t vs }}}
      stack_pop t
    {{{ w,
      RET w;
      (⌜vs = [] ∧ w = NONEV⌝ ∗ stack_model t []) ∨
      (∃ v vs', ⌜vs = v :: vs' ∧ w = SOMEV v⌝ ∗ stack_model t vs')
    }}} ;
}.
#[global] Arguments stack _ {_} : assert.
#[global] Arguments Build_stack {_ _ _ _ _ _ _ _} _ _ _ _ : assert.
#[global] Existing Instance stack_model_timeless.

Section std_stack.
  Context `{!heapGS Σ}.
  Implicit Types l : loc.
  Implicit Types v t lst : val.

  Definition std_stack_make : val :=
    λ: <>,
      ref (lst_nil #()).

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
        NONEV
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
    {{{ t, RET t; std_stack_model t [] }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (lst_nil_spec with "[//]"). iIntros "%lst #Hlst".
    wp_alloc l as "Hl".
    iApply "HΦ". iExists l, lst. naive_solver.
  Qed.

  Lemma std_stack_is_empty_spec t vs :
    {{{ std_stack_model t vs }}}
      std_stack_is_empty t
    {{{ RET #(bool_decide (vs = [])); std_stack_model t vs }}}.
  Proof.
    iIntros "%Φ (%l & %lst & -> & Hl & #Hlst) HΦ".
    wp_rec. wp_load.
    wp_apply (lst_is_empty_spec with "Hlst"). iIntros "_".
    iApply "HΦ". iExists l, lst. naive_solver.
  Qed.

  Lemma std_stack_push_spec t vs v :
    {{{ std_stack_model t vs }}}
      std_stack_push t v
    {{{ RET #(); std_stack_model t (v :: vs) }}}.
  Proof.
    iIntros "%Φ (%l & %lst & -> & Hl & #Hlst) HΦ".
    wp_rec. wp_load.
    wp_apply (lst_cons_spec with "Hlst"). iIntros "%lst' #Hlst'".
    wp_store.
    iApply "HΦ". iExists l, lst'. naive_solver.
  Qed.

  Lemma std_stack_pop_spec t vs :
    {{{ std_stack_model t vs }}}
      std_stack_pop t
    {{{ w,
      RET w;
      (⌜vs = [] ∧ w = NONEV⌝ ∗ std_stack_model t []) ∨
      (∃ v vs', ⌜vs = v :: vs' ∧ w = SOMEV v⌝ ∗ std_stack_model t vs')
    }}}.
  Proof.
    iIntros "%Φ (%l & %lst & -> & Hl & #Hlst) HΦ".
    wp_rec. wp_load. wp_pures.
    wp_apply (lst_is_empty_spec with "Hlst"). iIntros "_".
    destruct vs as [| v vs]; wp_pures.
    - iApply "HΦ". iLeft. repeat iSplitR; try done.
      iExists l, lst. naive_solver.
    - wp_apply (lst_tail_spec with "Hlst"); first done. iIntros "%lst' #Hlst'".
      wp_store.
      wp_apply (lst_head_spec with "Hlst"); first done. iIntros "_".
      wp_pures.
      iApply "HΦ". iRight. iExists v, vs. repeat iSplitR; try done.
      iExists l, lst'. naive_solver.
  Qed.

  Definition std_stack :=
    Build_stack
      std_stack_make_spec
      std_stack_is_empty_spec
      std_stack_push_spec
      std_stack_pop_spec.
End std_stack.

#[global] Typeclasses Opaque std_stack_model.
