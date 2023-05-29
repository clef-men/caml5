From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.std Require Export
  base.

Record deque `{!heapGS Σ} {unboxed : bool} := {
  deque_make : val ;
  deque_is_empty : val ;
  deque_push_front : val ;
  deque_pop_front : val ;
  deque_push_back : val ;
  deque_pop_back : val ;

  deque_model : val → list val → iProp Σ ;

  #[global] deque_model_timeless t vs ::
    Timeless (deque_model t vs) ;

  deque_make_spec :
    {{{ True }}}
      deque_make #()
    {{{ t,
      RET t;
      deque_model t []
    }}} ;

  deque_is_empty_spec t vs :
    {{{
      deque_model t vs
    }}}
      deque_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      deque_model t vs
    }}} ;

  deque_push_front_spec t vs v :
    {{{
      deque_model t vs
    }}}
      deque_push_front t v
    {{{
      RET #();
      deque_model t (v :: vs)
    }}} ;

  deque_pop_front_spec t vs :
    {{{
      deque_model t vs
    }}}
      deque_pop_front t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          deque_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          deque_model t vs'
      end
    }}} ;

  deque_push_back_spec t vs v :
    {{{
      deque_model t vs
    }}}
      deque_push_back t v
    {{{
      RET #();
      deque_model t (vs ++ [v])
    }}} ;

  deque_pop_back_spec t vs :
    {{{
      deque_model t vs
    }}}
      deque_pop_back t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          deque_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          deque_model t vs'
      end
    }}} ;

  deque_unboxed :
    if unboxed then ∀ t vs,
      deque_model t vs -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments deque _ {_} _ : assert.
#[global] Arguments Build_deque {_ _} _ {_ _ _ _ _ _ _ _} _ _ _ _ _ _ _ : assert.
