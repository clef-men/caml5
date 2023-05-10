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

Record mpsc_stack `{!heapGS Σ} {unboxed : bool} := {
  mpsc_stack_make : val ;
  mpsc_stack_push : val ;
  mpsc_stack_pop : val ;

  mpsc_stack_name : Type ;
  mpsc_stack_name_eq_dec :
    EqDecision mpsc_stack_name ;
  mpsc_stack_name_countable :
    Countable mpsc_stack_name ;

  mpsc_stack_inv : val → mpsc_stack_name → namespace → iProp Σ ;
  mpsc_stack_model : val → mpsc_stack_name → list val → iProp Σ ;
  mpsc_stack_consumer : val → mpsc_stack_name → iProp Σ ;

  mpsc_stack_inv_persistent t γ ι :
    Persistent (mpsc_stack_inv t γ ι) ;
  mpsc_stack_model_timeless t γ vs :
    Timeless (mpsc_stack_model t γ vs) ;
  mpsc_stack_consumer_timeless t γ :
    Timeless (mpsc_stack_consumer t γ) ;

  mpsc_stack_consumer_exclusive t γ :
    mpsc_stack_consumer t γ -∗
    mpsc_stack_consumer t γ -∗
    False ;

  mpsc_stack_make_spec ι :
    {{{ True }}}
      mpsc_stack_make #()
    {{{ t γ,
      RET t;
      mpsc_stack_inv t γ ι ∗
      mpsc_stack_model t γ [] ∗
      mpsc_stack_consumer t γ
    }}} ;

  mpsc_stack_push_spec t γ ι v :
    <<<
      mpsc_stack_inv t γ ι
    | ∀∀ vs, mpsc_stack_model t γ vs
    >>>
      mpsc_stack_push t v @ ↑ι
    <<<
      mpsc_stack_model t γ (v :: vs)
    | RET #(); True
    >>> ;

  mpsc_stack_pop_spec t γ ι :
    <<<
      mpsc_stack_inv t γ ι ∗
      mpsc_stack_consumer t γ
    | ∀∀ vs, mpsc_stack_model t γ vs
    >>>
      mpsc_stack_pop t @ ↑ι
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ mpsc_stack_model t γ []) ∨
      (∃ v vs', ⌜vs = v :: vs' ∧ o = SOMEV v⌝ ∗ mpsc_stack_model t γ vs')
    | RET o; mpsc_stack_consumer t γ
    >>> ;

  mpsc_stack_unboxed :
    if unboxed then ∀ t γ ι,
      mpsc_stack_inv t γ ι -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments mpsc_stack _ {_} _ : assert.
#[global] Arguments Build_mpsc_stack {_ _} _ {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ : assert.
#[global] Existing Instance mpsc_stack_name_eq_dec.
#[global] Existing Instance mpsc_stack_name_countable.
#[global] Existing Instance mpsc_stack_inv_persistent.
#[global] Existing Instance mpsc_stack_model_timeless.
#[global] Existing Instance mpsc_stack_consumer_timeless.

Class MpscStackOfMpmcStackG Σ `{!heapGS Σ} := {
  mpsc_stack_of_mpmc_stack_G_consumer_G : ExclG Σ unitO ;
}.
#[local] Existing Instance mpsc_stack_of_mpmc_stack_G_consumer_G.

Definition mpsc_stack_of_mpmc_stack_Σ := #[
  excl_Σ unitO
].
Lemma subG_mpsc_stack_of_mpmc_stack_Σ Σ `{!heapGS Σ} :
  subG mpsc_stack_of_mpmc_stack_Σ Σ →
  MpscStackOfMpmcStackG Σ.
Proof.
  solve_inG.
Qed.

Section mpsc_stack_of_mpmc_stack.
  Context `{mpsc_stack_of_mpmc_stack_G : MpscStackOfMpmcStackG Σ}.
  Context {unboxed} (mpmc_stack : mpmc_stack Σ unboxed).

  Notation "γ .(base)" := γ.1
  ( at level 5
  ) : stdpp_scope.
  Notation "γ .(consumer)" := γ.2
  ( at level 5
  ) : stdpp_scope.

  Program Definition mpsc_stack_of_mpmc_stack : mpsc_stack Σ unboxed := {|
    mpsc_stack_make :=
      mpmc_stack.(mpmc_stack_make) ;
    mpsc_stack_push :=
      mpmc_stack.(mpmc_stack_push) ;
    mpsc_stack_pop :=
      mpmc_stack.(mpmc_stack_pop) ;

    mpsc_stack_name :=
      mpmc_stack.(mpmc_stack_name) * gname ;
    mpsc_stack_inv t γ ι :=
      mpmc_stack.(mpmc_stack_inv) t γ.(base) ι ;
    mpsc_stack_model t γ :=
      mpmc_stack.(mpmc_stack_model) t γ.(base) ;
    mpsc_stack_consumer _ γ :=
      excl γ.(consumer) () ;
  |}.
  Next Obligation.
    intros. apply excl_exclusive.
  Qed.
  Next Obligation.
    iIntros "%ι %Φ _ HΦ".
    iMod excl_alloc as "(%γ_consumer & Hconsumer)".
    wp_apply (mpmc_stack_make_spec with "[//]"). iIntros "%t %γ_base (Hinv & Hmodel)".
    iApply ("HΦ" $! t (γ_base, γ_consumer)). iFrame.
  Qed.
  Next Obligation.
    intros. apply mpmc_stack_push_spec.
  Qed.
  Next Obligation.
    iIntros "%t %γ %ι !> %Φ (Hinv & Hconsumer) HΦ".
    wp_apply (mpmc_stack_pop_spec with "Hinv").
    iApply (atomic_update_wand with "[Hconsumer] HΦ").
    iIntros "_ %v HΦ _". iApply "HΦ". done.
  Qed.
  Next Obligation.
    destruct unboxed; last done. eauto using mpmc_stack.(mpmc_stack_unboxed).
  Qed.
End mpsc_stack_of_mpmc_stack.
