From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.concurrent Require Export
  counter.

Implicit Types v t : val.
Implicit Types vs : list val.
Implicit Types vss : list (list val).

Record ws_deques `{!heapGS Σ} `{counter_G : !CounterG Σ} {unboxed : bool} := {
  ws_deques_make : val ;
  ws_deques_size : val ;
  ws_deques_push : val ;
  ws_deques_pop : val ;
  ws_deques_steal : val ;

  ws_deques_name : Type ;
  ws_deques_name_eq_dec :
    EqDecision ws_deques_name ;
  ws_deques_name_countable :
    Countable ws_deques_name ;

  ws_deques_inv : val → ws_deques_name → namespace → val → nat → iProp Σ ;
  ws_deques_model : val → ws_deques_name → list (list val) → iProp Σ ;

  ws_deques_inv_persistent t γ ι cntr sz :
    Persistent (ws_deques_inv t γ ι cntr sz) ;
  ws_deques_model_timeless t γ vss :
    Timeless (ws_deques_model t γ vss) ;

  ws_deques_inv_valid t γ ι cntr sz :
    ws_deques_inv t γ ι cntr sz -∗
    ∃ ι_cntr, counter_inv cntr ι_cntr (Some sz) ;

  ws_deques_make_spec ι cntr ι_cntr sz sz' :
    sz' = Z.of_nat sz →
    {{{
      counter_inv cntr ι_cntr (Some sz)
    }}}
      ws_deques_make #sz'
    {{{ t γ,
      RET t;
      ws_deques_inv t γ ι cntr sz ∗
      ws_deques_model t γ (repeat [] sz)
    }}} ;

  ws_deques_size_spec t γ ι cntr sz :
    {{{
      ws_deques_inv t γ ι cntr sz
    }}}
      ws_deques_size t
    {{{
      RET #sz; True
    }}} ;

  ws_deques_push_spec t γ ι cntr sz i i' v :
    i' = Z.of_nat i →
    <<<
      ws_deques_inv t γ ι cntr sz ∗
      counter_token cntr i
    | ∀∀ vss, ws_deques_model t γ vss
    >>>
      ws_deques_push t #i' v @ ↑ι
    <<< ∃∃ vs,
      ⌜vss !! i = Some vs⌝ ∗
      ws_deques_model t γ (<[i := vs ++ [v]]> vss)
    | RET #(); counter_token cntr i
    >>> ;

  ws_deques_pop_spec t γ ι cntr sz i i' :
    i' = Z.of_nat i →
    <<<
      ws_deques_inv t γ ι cntr sz ∗
      counter_token cntr i
    | ∀∀ vss, ws_deques_model t γ vss
    >>>
      ws_deques_pop t #i' @ ↑ι
    <<< ∃∃ o,
        ⌜vss !! i = Some [] ∧ o = NONEV⌝ ∗
        ws_deques_model t γ vss
      ∨ ∃ vs v,
        ⌜vss !! i = Some (vs ++ [v]) ∧ o = SOMEV v⌝ ∗
        ws_deques_model t γ (<[i := vs]> vss)
    | RET o; counter_token cntr i
    >>> ;

  ws_deques_steal_spec t γ ι cntr (sz : nat) i :
    (0 ≤ i < sz)%Z →
    <<<
      ws_deques_inv t γ ι cntr sz
    | ∀∀ vss, ws_deques_model t γ vss
    >>>
      ws_deques_steal t #i @ ↑ι
    <<< ∃∃ o,
      let i := Z.to_nat i in
        ⌜vss !! i = Some [] ∧ o = NONEV⌝ ∗
        ws_deques_model t γ vss
      ∨ ∃ v vs,
        ⌜vss !! i = Some (v :: vs) ∧ o = SOMEV v⌝ ∗
        ws_deques_model t γ (<[i := vs]> vss)
    | RET o; True
    >>> ;

  ws_deques_unboxed :
    if unboxed then ∀ t γ ι cntr sz,
      ws_deques_inv t γ ι cntr sz -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments ws_deques _ {_ _} _ : assert.
#[global] Arguments Build_ws_deques {_ _ _ _} _ {_ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ : assert.
#[global] Existing Instance ws_deques_name_eq_dec.
#[global] Existing Instance ws_deques_name_countable.
#[global] Existing Instance ws_deques_inv_persistent.
#[global] Existing Instance ws_deques_model_timeless.
