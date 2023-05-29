From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.concurrent Require Export
  base.

Implicit Types v t : val.
Implicit Types vs : list val.

Record mpmc_stack `{!heapGS Σ} {unboxed : bool} := {
  mpmc_stack_make : val ;
  mpmc_stack_push : val ;
  mpmc_stack_pop : val ;

  mpmc_stack_name : Type ;
  #[global] mpmc_stack_name_eq_dec ::
    EqDecision mpmc_stack_name ;
  #[global] mpmc_stack_name_countable ::
    Countable mpmc_stack_name ;

  mpmc_stack_inv : val → mpmc_stack_name → namespace → iProp Σ ;
  mpmc_stack_model : val → mpmc_stack_name → list val → iProp Σ ;

  #[global] mpmc_stack_inv_persistent t γ ι ::
    Persistent (mpmc_stack_inv t γ ι) ;
  #[global] mpmc_stack_model_timeless t γ vs ::
    Timeless (mpmc_stack_model t γ vs) ;

  mpmc_stack_make_spec ι :
    {{{ True }}}
      mpmc_stack_make #()
    {{{ t γ,
      RET t;
      mpmc_stack_inv t γ ι ∗
      mpmc_stack_model t γ []
    }}} ;

  mpmc_stack_push_spec t γ ι v :
    <<<
      mpmc_stack_inv t γ ι
    | ∀∀ vs, mpmc_stack_model t γ vs
    >>>
      mpmc_stack_push t v @ ↑ι
    <<<
      mpmc_stack_model t γ (v :: vs)
    | RET #(); True
    >>> ;

  mpmc_stack_pop_spec t γ ι :
    <<<
      mpmc_stack_inv t γ ι
    | ∀∀ vs, mpmc_stack_model t γ vs
    >>>
      mpmc_stack_pop t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          mpmc_stack_model t γ []
      | Some v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          mpmc_stack_model t γ vs'
      end
    | RET o; True
    >>> ;

  mpmc_stack_unboxed :
    if unboxed then ∀ t γ ι,
      mpmc_stack_inv t γ ι -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments mpmc_stack _ {_} _ : assert.
#[global] Arguments Build_mpmc_stack {_ _} _ {_ _ _ _ _ _ _ _ _ _} _ _ _ _ : assert.
