From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.std Require Export
  base.

Record stack `{!heapGS Σ} {unboxed : bool} := {
  stack_make : val ;
  stack_is_empty : val ;
  stack_push : val ;
  stack_pop : val ;

  stack_model : val → list val → iProp Σ ;

  #[global] stack_model_timeless t vs ::
    Timeless (stack_model t vs) ;

  stack_make_spec :
    {{{ True }}}
      stack_make #()
    {{{ t,
      RET t;
      stack_model t []
    }}} ;

  stack_is_empty_spec t vs :
    {{{
      stack_model t vs
    }}}
      stack_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      stack_model t vs
    }}} ;

  stack_push_spec t vs v :
    {{{
      stack_model t vs
    }}}
      stack_push t v
    {{{
      RET #();
      stack_model t (v :: vs)
    }}} ;

  stack_pop_spec t vs :
    {{{
      stack_model t vs
    }}}
      stack_pop t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          stack_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          stack_model t vs'
      end
    }}} ;

    stack_unboxed :
      if unboxed then ∀ t vs,
        stack_model t vs -∗
        ⌜val_is_unboxed t⌝
      else
        True ;
}.
#[global] Arguments stack _ {_} _ : assert.
#[global] Arguments Build_stack {_ _} _ {_ _ _ _ _ _} _ _ _ _ _ : assert.
