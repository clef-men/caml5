From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.std Require Export
  base.

Record fun_stack `{!heapGS Σ} {unboxed : bool} := {
  fun_stack_make : val ;
  fun_stack_is_empty : val ;
  fun_stack_push : val ;
  fun_stack_pop : val ;

  fun_stack_model : val → list val → iProp Σ ;

  #[global] fun_stack_model_persistent t vs ::
    Persistent (fun_stack_model t vs) ;
  #[global] fun_stack_model_timeless t vs ::
    Timeless (fun_stack_model t vs) ;

  fun_stack_make_spec :
    {{{ True }}}
      fun_stack_make #()
    {{{ t,
      RET t;
      fun_stack_model t []
    }}} ;

  fun_stack_is_empty_spec t vs :
    {{{
      fun_stack_model t vs
    }}}
      fun_stack_is_empty t
    {{{
      RET #(bool_decide (vs = []));
      True
    }}} ;

  fun_stack_push_spec t vs v :
    {{{
      fun_stack_model t vs
    }}}
      fun_stack_push t v
    {{{ t',
      RET t';
      fun_stack_model t' (v :: vs)
    }}} ;

  fun_stack_pop_spec t vs :
    {{{
      fun_stack_model t vs
    }}}
      fun_stack_pop t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝
      | Some p =>
          ∃ v vs' t',
          ⌜vs = v :: vs' ∧ p = (v, t')%V⌝ ∗
          fun_stack_model t' vs'
      end
    }}} ;

  fun_stack_unboxed :
    if unboxed then ∀ t vs,
      fun_stack_model t vs -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments fun_stack _ {_} _ : assert.
#[global] Arguments Build_fun_stack {_ _} _ {_ _ _ _ _ _ _} _ _ _ _ _ : assert.
