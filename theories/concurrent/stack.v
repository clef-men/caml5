From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.concurrent Require Export
  base.

Implicit Types v t : val.
Implicit Types vs : list val.

Record stack `{!heapGS Σ} := {
  stack_make : val ;
  stack_push : val ;
  stack_pop : val ;

  stack_namespace : namespace ;
  stack_inv : val → iProp Σ ;
  stack_model : val → list val → iProp Σ ;

  stack_inv_persistent t :
    Persistent (stack_inv t) ;
  stack_model_timeless t vs :
    Timeless (stack_model t vs) ;

  stack_make_spec :
    {{{ True }}}
      stack_make #()
    {{{ t, RET t; stack_inv t ∗ stack_model t [] }}} ;

  stack_push_spec t v :
    <<< stack_inv t | ∀∀ vs, stack_model t vs >>>
      stack_push t v
      @ ↑ stack_namespace
    <<< stack_model t (v :: vs) | RET #(); True >>> ;

  stack_pop_spec t :
    <<< stack_inv t | ∀∀ vs, stack_model t vs >>>
      stack_pop t
      @ ↑ stack_namespace
    <<< ∃∃ w,
      (⌜vs = [] ∧ w = NONEV⌝ ∗ stack_model t []) ∨
      (∃ v vs', ⌜w = SOMEV v ∧ vs = v :: vs'⌝ ∗ stack_model t vs') |
      RET w; True
    >>> ;
}.
#[global] Arguments stack _ {_} : assert.
#[global] Arguments Build_stack {_ _ _ _ _ _ _ _ _ _} _ _ _ : assert.
#[global] Existing Instance stack_inv_persistent.
#[global] Existing Instance stack_model_timeless.
