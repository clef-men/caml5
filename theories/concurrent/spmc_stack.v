From caml5 Require Import
  prelude.
From caml5.base_logic Require Import
  lib.excl.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.concurrent Require Export
  base.
From caml5.concurrent Require Import
  mpmc_stack.

Implicit Types v t : val.
Implicit Types vs : list val.

Record spmc_stack `{!heapGS Σ} {unboxed : bool} := {
  spmc_stack_make : val ;
  spmc_stack_push : val ;
  spmc_stack_pop : val ;

  spmc_stack_name : Type ;
  #[global] spmc_stack_name_eq_dec ::
    EqDecision spmc_stack_name ;
  #[global] spmc_stack_name_countable ::
    Countable spmc_stack_name ;

  spmc_stack_inv : val → spmc_stack_name → namespace → iProp Σ ;
  spmc_stack_model : val → spmc_stack_name → list val → iProp Σ ;
  spmc_stack_producer : val → spmc_stack_name → iProp Σ ;

  #[global] spmc_stack_inv_persistent t γ ι ::
    Persistent (spmc_stack_inv t γ ι) ;
  #[global] spmc_stack_model_timeless t γ vs ::
    Timeless (spmc_stack_model t γ vs) ;
  #[global] spmc_stack_producer_timeless t γ ::
    Timeless (spmc_stack_producer t γ) ;

  spmc_stack_producer_exclusive t γ :
    spmc_stack_producer t γ -∗
    spmc_stack_producer t γ -∗
    False ;

  spmc_stack_make_spec ι :
    {{{ True }}}
      spmc_stack_make #()
    {{{ t γ,
      RET t;
      spmc_stack_inv t γ ι ∗
      spmc_stack_model t γ [] ∗
      spmc_stack_producer t γ
    }}} ;

  spmc_stack_push_spec t γ ι v :
    <<<
      spmc_stack_inv t γ ι ∗
      spmc_stack_producer t γ
    | ∀∀ vs, spmc_stack_model t γ vs
    >>>
      spmc_stack_push t v @ ↑ι
    <<<
      spmc_stack_model t γ (v :: vs)
    | RET #();
      spmc_stack_producer t γ
    >>> ;

  spmc_stack_pop_spec t γ ι :
    <<<
      spmc_stack_inv t γ ι
    | ∀∀ vs, spmc_stack_model t γ vs
    >>>
      spmc_stack_pop t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          spmc_stack_model t γ []
      | Some v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          spmc_stack_model t γ vs'
      end
    | RET o; True
    >>> ;

  spmc_stack_unboxed :
    if unboxed then ∀ t γ ι,
      spmc_stack_inv t γ ι -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments spmc_stack _ {_} _ : assert.
#[global] Arguments Build_spmc_stack {_ _} _ {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ : assert.

Class SpmcStackOfMpmcStackG Σ `{!heapGS Σ} := {
  #[local] spmc_stack_of_mpmc_stack_G_producer_G :: ExclG Σ unitO ;
}.

Definition spmc_stack_of_mpmc_stack_Σ := #[
  excl_Σ unitO
].
Lemma subG_spmc_stack_of_mpmc_stack_Σ Σ `{!heapGS Σ} :
  subG spmc_stack_of_mpmc_stack_Σ Σ →
  SpmcStackOfMpmcStackG Σ.
Proof.
  solve_inG.
Qed.

Program Coercion spmc_stack_of_mpmc_stack
  `{spmc_stack_of_mpmc_stack_G : SpmcStackOfMpmcStackG Σ}
  {unboxed} (mpmc_stack : mpmc_stack Σ unboxed)
  : spmc_stack Σ unboxed
:= {|
  spmc_stack_make :=
    mpmc_stack.(mpmc_stack_make) ;
  spmc_stack_push :=
    mpmc_stack.(mpmc_stack_push) ;
  spmc_stack_pop :=
    mpmc_stack.(mpmc_stack_pop) ;

  spmc_stack_name :=
    mpmc_stack.(mpmc_stack_name) * gname ;
  spmc_stack_inv t γ ι :=
    mpmc_stack.(mpmc_stack_inv) t γ.1 ι ;
  spmc_stack_model t γ :=
    mpmc_stack.(mpmc_stack_model) t γ.1 ;
  spmc_stack_producer _ γ :=
    excl γ.2 () ;
|}.
Next Obligation.
  intros. apply excl_exclusive.
Qed.
Next Obligation.
  iIntros "* _ HΦ".
  iMod excl_alloc as "(%γ_producer & Hproducer)".
  wp_apply (mpmc_stack_make_spec with "[//]"). iIntros "%t %γ_base (Hinv & Hmodel)".
  iApply ("HΦ" $! t (γ_base, γ_producer)). iFrame.
Qed.
Next Obligation.
  iIntros "* !> %Φ (Hinv & Hproducer) HΦ".
  wp_apply (mpmc_stack_push_spec with "Hinv").
  iApply (atomic_update_wand with "[Hproducer] HΦ").
  iIntros "_ HΦ _". iApply "HΦ". done.
Qed.
Next Obligation.
  intros. apply mpmc_stack_pop_spec.
Qed.
Next Obligation.
  intros. destruct unboxed; last done.
  eauto using mpmc_stack.(mpmc_stack_unboxed).
Qed.
