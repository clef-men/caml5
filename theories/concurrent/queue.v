From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.concurrent Require Export
  base.

Implicit Types v w t : val.
Implicit Types vs : list val.

Record queue `{!heapGS Σ} := {
  queue_make : val ;
  queue_push : val ;
  queue_pop : val ;

  queue_namespace : namespace ;
  queue_inv : val → iProp Σ ;
  queue_model : val → list val → iProp Σ ;

  queue_inv_persistent t :
    Persistent (queue_inv t) ;
  queue_model_timeless t vs :
    Timeless (queue_model t vs) ;

  queue_make_spec :
    {{{ True }}}
      queue_make #()
    {{{ t, RET t; queue_inv t ∗ queue_model t [] }}} ;

  queue_push_spec t v :
    <<< queue_inv t | ∀∀ vs, queue_model t vs >>>
      queue_push t v
      @ ↑ queue_namespace
    <<< queue_model t (v :: vs) | RET #(); True >>> ;

  queue_pop_spec t :
    <<< queue_inv t | ∀∀ vs, queue_model t vs >>>
      queue_pop t
      @ ↑ queue_namespace
    <<< ∃∃ w,
      (⌜vs = [] ∧ w = NONEV⌝ ∗ queue_model t []) ∨
      (∃ vs' v, ⌜w = SOMEV v ∧ vs = vs' ++ [v]⌝ ∗ queue_model t vs') |
      RET w; True
    >>> ;
}.
#[global] Arguments queue _ {_} : assert.
#[global] Arguments Build_queue {_ _ _ _ _ _ _ _ _ _} _ _ _ : assert.
#[global] Existing Instance queue_inv_persistent.
#[global] Existing Instance queue_model_timeless.
