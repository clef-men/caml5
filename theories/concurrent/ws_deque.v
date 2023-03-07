From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.concurrent Require Export
  base.

Implicit Types v w t : val.
Implicit Types vs : list val.

Record ws_deque `{!heapGS Σ} := {
  ws_deque_make : val ;
  ws_deque_push : val ;
  ws_deque_pop : val ;
  ws_deque_steal : val ;

  ws_deque_namespace : namespace ;
  ws_deque_inv : val → iProp Σ ;
  ws_deque_model : val → list val → iProp Σ ;
  ws_deque_own : val → iProp Σ ;

  ws_deque_inv_persistent t :
    Persistent (ws_deque_inv t) ;
  ws_deque_model_timeless t vs :
    Timeless (ws_deque_model t vs) ;
  ws_deque_own_timeless t :
    Timeless (ws_deque_own t) ;

  ws_deque_own_exclusive t :
    ws_deque_own t -∗
    ws_deque_own t -∗
    False ;

  ws_deque_make_spec :
    {{{ True }}}
      ws_deque_make #()
    {{{ t, RET t; ws_deque_inv t ∗ ws_deque_model t [] ∗ ws_deque_own t }}} ;

  ws_deque_push_spec t v :
    <<<
      ws_deque_inv t ∗ ws_deque_own t |
      ∀∀ vs, ws_deque_model t vs
    >>>
      ws_deque_push t v
      @ ↑ ws_deque_namespace
    <<<
      ws_deque_model t (vs ++ [v]) |
      RET #(); ws_deque_own t
    >>> ;

  ws_deque_pop_spec t :
    <<<
      ws_deque_inv t ∗ ws_deque_own t |
      ∀∀ vs, ws_deque_model t vs
    >>>
      ws_deque_pop t
      @ ↑ ws_deque_namespace
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ ws_deque_model t []) ∨
      (∃ vs' v, ⌜vs = vs' ++ [v] ∧ o = SOMEV v⌝ ∗ ws_deque_model t vs') |
      RET o; ws_deque_own t
    >>> ;

  ws_deque_steal_spec t :
    <<<
      ws_deque_inv t |
      ∀∀ vs, ws_deque_model t vs
    >>>
      ws_deque_steal t
      @ ↑ ws_deque_namespace
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ ws_deque_model t []) ∨
      (∃ v vs', ⌜vs = v :: vs' ∧ o = SOMEV v⌝ ∗ ws_deque_model t vs') |
      RET o; True
    >>> ;
}.
#[global] Arguments ws_deque _ {_} : assert.
#[global] Arguments Build_ws_deque {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ : assert.
#[global] Existing Instance ws_deque_inv_persistent.
#[global] Existing Instance ws_deque_model_timeless.
#[global] Existing Instance ws_deque_own_timeless.
