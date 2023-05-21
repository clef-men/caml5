From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.std Require Export
  base.

Record queue `{!heapGS Σ} {unboxed : bool} := {
  queue_make : val ;
  queue_is_empty : val ;
  queue_push : val ;
  queue_pop : val ;

  queue_model : val → list val → iProp Σ ;

  queue_model_timeless t vs :
    Timeless (queue_model t vs) ;

  queue_make_spec :
    {{{ True }}}
      queue_make #()
    {{{ t,
      RET t;
      queue_model t []
    }}} ;

  queue_is_empty_spec t vs :
    {{{
      queue_model t vs
    }}}
      queue_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      queue_model t vs
    }}} ;

  queue_push_spec t vs v :
    {{{
      queue_model t vs
    }}}
      queue_push t v
    {{{
      RET #();
      queue_model t (v :: vs)
    }}} ;

  queue_pop_spec t vs :
    {{{
      queue_model t vs
    }}}
      queue_pop t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          queue_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          queue_model t vs'
      end
    }}} ;

  queue_unboxed :
    if unboxed then ∀ t vs,
      queue_model t vs -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments queue _ {_} _ : assert.
#[global] Arguments Build_queue {_ _} _ {_ _ _ _ _ _} _ _ _ _ _ : assert.
#[global] Existing Instance queue_model_timeless.
