From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.
From caml5.std Require Import
  lst
  fun_stack.

Section heapGS.
  Context `{!heapGS Σ}.
  Implicit Types v t lst : val.

  Definition std_fun_stack_make : val :=
    λ: <>,
      lst_nil.

  Definition std_fun_stack_is_empty :=
    lst_is_empty.

  Definition std_fun_stack_push : val :=
    λ: "t" "v",
      lst_cons "v" "t".

  Definition std_fun_stack_pop : val :=
    λ: "t",
      if: lst_is_empty "t" then (
        NONE
      ) else (
        SOME (lst_head "t", lst_tail "t")
      ).

  Definition std_fun_stack_model t vs : iProp Σ :=
    lst_model t vs.

  #[global] Instance std_fun_stack_model_persistent t vs :
    Persistent (std_fun_stack_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance std_fun_stack_model_timeless t vs :
    Timeless (std_fun_stack_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma std_fun_stack_make_spec :
    {{{ True }}}
      std_fun_stack_make #()
    {{{ t,
      RET t;
      std_fun_stack_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    iApply "HΦ". iApply lst_nil_spec.
  Qed.

  Lemma std_fun_stack_is_empty_spec t vs :
    {{{
      std_fun_stack_model t vs
    }}}
      std_fun_stack_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      True
    }}}.
  Proof.
    iIntros "%Φ #Hlst HΦ".
    wp_apply (lst_is_empty_spec with "Hlst"). done.
  Qed.

  Lemma std_fun_stack_push_spec t vs v :
    {{{
      std_fun_stack_model t vs
    }}}
      std_fun_stack_push t v
    {{{ t',
      RET t';
      std_fun_stack_model t' (v :: vs)
    }}}.
  Proof.
    iIntros "%Φ #Hlst HΦ".
    rewrite /std_fun_stack_push. wp_pures.
    wp_apply (lst_cons_spec with "Hlst"). iIntros "%lst' #Hlst'".
    iApply ("HΦ" with "Hlst'").
  Qed.

  Lemma std_fun_stack_pop_spec t vs :
    {{{
      std_fun_stack_model t vs
    }}}
      std_fun_stack_pop t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝
      | Some p =>
          ∃ v vs' t',
          ⌜vs = v :: vs' ∧ p = (v, t')%V⌝ ∗
          std_fun_stack_model t' vs'
      end
    }}}.
  Proof.
    iIntros "%Φ #Hlst HΦ".
    wp_rec.
    wp_apply (lst_is_empty_spec with "Hlst"). iIntros "_".
    destruct vs as [| v vs]; wp_pures.
    - iApply ("HΦ" $! None). done.
    - wp_apply (lst_tail_spec with "Hlst"); first done. iIntros "%lst' #Hlst'".
      wp_apply (lst_head_spec with "Hlst"); first done. iIntros "_".
      wp_pures.
      iApply ("HΦ" $! (Some (v, lst')%V)). iExists v, vs, lst'. auto with iFrame.
  Qed.

  Definition std_fun_stack :=
    Build_fun_stack false
      std_fun_stack_make_spec
      std_fun_stack_is_empty_spec
      std_fun_stack_push_spec
      std_fun_stack_pop_spec
      I.
End heapGS.

#[global] Opaque std_fun_stack_make.
#[global] Opaque std_fun_stack_is_empty.
#[global] Opaque std_fun_stack_push.
#[global] Opaque std_fun_stack_pop.

#[global] Opaque std_fun_stack_model.
