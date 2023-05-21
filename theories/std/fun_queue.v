From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.std Require Export
  base.

Record fun_queue `{!heapGS Σ} {unboxed : bool} := {
  fun_queue_make : val ;
  fun_queue_is_empty : val ;
  fun_queue_push : val ;
  fun_queue_pop : val ;

  fun_queue_model : val → list val → iProp Σ ;

  fun_queue_model_persistent t vs :
    Persistent (fun_queue_model t vs) ;
  fun_queue_model_timeless t vs :
    Timeless (fun_queue_model t vs) ;

  fun_queue_make_spec :
    {{{ True }}}
      fun_queue_make #()
    {{{ t,
      RET t;
      fun_queue_model t []
    }}} ;

  fun_queue_is_empty_spec t vs :
    {{{
      fun_queue_model t vs
    }}}
      fun_queue_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      True
    }}} ;

  fun_queue_push_spec t vs v :
    {{{
      fun_queue_model t vs
    }}}
      fun_queue_push t v
    {{{ t',
      RET t';
      fun_queue_model t' (v :: vs)
    }}} ;

  fun_queue_pop_spec t vs :
    {{{
      fun_queue_model t vs
    }}}
      fun_queue_pop t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝
      | Some p =>
          ∃ vs' v t',
          ⌜vs = vs' ++ [v] ∧ p = (v, t')%V⌝ ∗
          fun_queue_model t' vs'
      end
    }}} ;

  fun_queue_unboxed :
    if unboxed then ∀ t vs,
      fun_queue_model t vs -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments fun_queue _ {_} _ : assert.
#[global] Arguments Build_fun_queue {_ _} _ {_ _ _ _ _ _ _} _ _ _ _ _ : assert.
#[global] Existing Instance fun_queue_model_persistent.
#[global] Existing Instance fun_queue_model_timeless.
