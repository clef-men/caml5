From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.concurrent Require Export
  base.

Implicit Types v w t : val.
Implicit Types vs : list val.

Record ws_deque `{!heapGS Σ} {unboxed : bool} := {
  ws_deque_make : val ;
  ws_deque_push : val ;
  ws_deque_pop : val ;
  ws_deque_steal : val ;

  ws_deque_name : Type ;
  ws_deque_inv : val → ws_deque_name → namespace → iProp Σ ;
  ws_deque_model : val → ws_deque_name → list val → iProp Σ ;
  ws_deque_owner : val → ws_deque_name → iProp Σ ;

  ws_deque_inv_persistent t γ ι :
    Persistent (ws_deque_inv t γ ι) ;
  ws_deque_model_timeless t γ vs :
    Timeless (ws_deque_model t γ vs) ;
  ws_deque_owner_timeless t γ :
    Timeless (ws_deque_owner t γ) ;

  ws_deque_owner_exclusive t γ :
    ws_deque_owner t γ -∗
    ws_deque_owner t γ -∗
    False ;

  ws_deque_make_spec ι :
    {{{ True }}}
      ws_deque_make #()
    {{{ t γ, RET t; ws_deque_inv t γ ι ∗ ws_deque_model t γ [] ∗ ws_deque_owner t γ }}} ;

  ws_deque_push_spec t γ ι v :
    <<<
      ws_deque_inv t γ ι ∗ ws_deque_owner t γ |
      ∀∀ vs, ws_deque_model t γ vs
    >>>
      ws_deque_push t v
      @ ↑ ι
    <<<
      ws_deque_model t γ (vs ++ [v]) |
      RET #(); ws_deque_owner t γ
    >>> ;

  ws_deque_pop_spec t γ ι :
    <<<
      ws_deque_inv t γ ι ∗ ws_deque_owner t γ |
      ∀∀ vs, ws_deque_model t γ vs
    >>>
      ws_deque_pop t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ ws_deque_model t γ []) ∨
      (∃ vs' v, ⌜vs = vs' ++ [v] ∧ o = SOMEV v⌝ ∗ ws_deque_model t γ vs') |
      RET o; ws_deque_owner t γ
    >>> ;

  ws_deque_steal_spec t γ ι :
    <<<
      ws_deque_inv t γ ι |
      ∀∀ vs, ws_deque_model t γ vs
    >>>
      ws_deque_steal t
      @ ↑ ι
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ ws_deque_model t γ []) ∨
      (∃ v vs', ⌜vs = v :: vs' ∧ o = SOMEV v⌝ ∗ ws_deque_model t γ vs') |
      RET o; True
    >>> ;

  ws_deque_unboxed :
    if unboxed then ∀ t γ ι,
      ws_deque_inv t γ ι -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments ws_deque _ {_} _ : assert.
#[global] Arguments Build_ws_deque {_ _} _ {_ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ : assert.
#[global] Existing Instance ws_deque_inv_persistent.
#[global] Existing Instance ws_deque_model_timeless.
#[global] Existing Instance ws_deque_owner_timeless.
