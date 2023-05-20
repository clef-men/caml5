From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.concurrent Require Export
  base.

Implicit Types v t : val.
Implicit Types vs : list val.

Record mpmc_queue `{!heapGS Σ} {unboxed : bool} := {
  mpmc_queue_make : val ;
  mpmc_queue_push : val ;
  mpmc_queue_pop : val ;

  mpmc_queue_name : Type ;
  mpmc_queue_name_eq_dec :
    EqDecision mpmc_queue_name ;
  mpmc_queue_name_countable :
    Countable mpmc_queue_name ;

  mpmc_queue_inv : val → mpmc_queue_name → namespace → iProp Σ ;
  mpmc_queue_model : val → mpmc_queue_name → list val → iProp Σ ;

  mpmc_queue_inv_persistent t γ ι :
    Persistent (mpmc_queue_inv t γ ι) ;
  mpmc_queue_model_timeless t γ vs :
    Timeless (mpmc_queue_model t γ vs) ;

  mpmc_queue_make_spec ι :
    {{{ True }}}
      mpmc_queue_make #()
    {{{ t γ,
      RET t;
      mpmc_queue_inv t γ ι ∗
      mpmc_queue_model t γ []
    }}} ;

  mpmc_queue_push_spec t γ ι v :
    <<<
      mpmc_queue_inv t γ ι
    | ∀∀ vs, mpmc_queue_model t γ vs
    >>>
      mpmc_queue_push t v @ ↑ι
    <<<
      mpmc_queue_model t γ (v :: vs)
    | RET #(); True
    >>> ;

  mpmc_queue_pop_spec t γ ι :
    <<<
      mpmc_queue_inv t γ ι
    | ∀∀ vs, mpmc_queue_model t γ vs
    >>>
      mpmc_queue_pop t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          mpmc_queue_model t γ []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          mpmc_queue_model t γ vs'
      end
    | RET o; True
    >>> ;

  mpmc_queue_unboxed :
  if unboxed then ∀ t γ ι,
    mpmc_queue_inv t γ ι -∗
    ⌜val_is_unboxed t⌝
  else
    True ;
}.
#[global] Arguments mpmc_queue _ {_} _ : assert.
#[global] Arguments Build_mpmc_queue {_ _} _ {_ _ _ _ _ _ _ _ _ _} _ _ _ _ : assert.
#[global] Existing Instance mpmc_queue_name_eq_dec.
#[global] Existing Instance mpmc_queue_name_countable.
#[global] Existing Instance mpmc_queue_inv_persistent.
#[global] Existing Instance mpmc_queue_model_timeless.
