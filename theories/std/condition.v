From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  mutex.

Record condition `{!heapGS Σ} {mutex : mutex Σ} := {
  condition_make : val ;
  condition_wait : val ;
  condition_signal : val ;
  condition_broadcast : val ;

  condition_inv : val → iProp Σ ;

  condition_inv_persistent t :
    Persistent (condition_inv t) ;

  condition_make_spec :
    {{{ True }}}
      condition_make #()
    {{{ t, RET t; condition_inv t }}} ;

  condition_wait_spec t mtx P :
    {{{ condition_inv t ∗ mutex.(mutex_inv) mtx P ∗ mutex.(mutex_locked) mtx ∗ P }}}
      condition_wait t mtx
    {{{ RET #(); mutex.(mutex_locked) mtx ∗ P }}} ;

  condition_signal_spec t :
    {{{ condition_inv t }}}
      condition_signal t
    {{{ RET #(); True }}} ;

  condition_broadcast_spec t :
    {{{ condition_inv t }}}
      condition_broadcast t
    {{{ RET #(); True }}} ;
}.
#[global] Arguments condition _ {_} _ : assert.
#[global] Arguments Build_condition {_ _ _ _ _ _ _ _ _} _ _ _ _ : assert.
#[global] Existing Instance condition_inv_persistent.

Section condition.
  Context `{!heapGS Σ} {mutex : mutex Σ} (condition : condition Σ mutex).

  #[local] Definition condition_wait_until_aux (cond : val) : val :=
    rec: "condition_wait_until_aux" "t" "mtx" :=
      if: cond #() then #() else (
        condition.(condition_wait) "t" "mtx" ;;
        "condition_wait_until_aux" "t" "mtx"
      ).
  Definition condition_wait_until cond : val :=
    λ: "t" "mtx",
      condition_wait_until_aux cond "t" "mtx".

  Definition condition_wait_while (cond : val) :=
    condition_wait_until (λ: <>, ~ cond #()).

  Lemma condition_wait_until_spec (cond : val) t mtx P Φ :
    {{{
      condition.(condition_inv) t ∗ mutex.(mutex_inv) mtx P ∗
      mutex.(mutex_locked) mtx ∗ P ∗ Φ false ∗
      {{{ mutex.(mutex_locked) mtx ∗ P ∗ Φ false }}}
        cond #()
      {{{ (b : bool), RET #b; mutex.(mutex_locked) mtx ∗ P ∗ Φ b }}}
    }}}
      condition_wait_until cond t mtx
    {{{
      RET #();
      mutex.(mutex_locked) mtx ∗ P ∗ Φ true
    }}}.
  Proof.
    iIntros "%Ψ (#Hinv_t & #Hinv_mtx & Hlocked & HP & HΦ & #Hcond) HΨ".
    wp_rec. wp_pures.
    iLöb as "HLöb".
    wp_rec. wp_pures.
    wp_apply ("Hcond" with "[$]"). iIntros "%b (Hlocked & HP & HΦ)".
    destruct b; wp_pures.
    { iApply "HΨ". iFrame. done. }
    wp_apply (condition_wait_spec _  _ _ P with "[$]"). iIntros "(Hlocked & HP)".
    wp_pures.
    iApply ("HLöb" with "[$] [$] [$] [$]").
  Qed.

  Lemma condition_wait_while_spec (cond : val) t mtx P Φ :
    {{{
      condition.(condition_inv) t ∗ mutex.(mutex_inv) mtx P ∗
      mutex.(mutex_locked) mtx ∗ P ∗ Φ true ∗
      {{{ mutex.(mutex_locked) mtx ∗ P ∗ Φ true }}}
        cond #()
      {{{ (b : bool), RET #b; mutex.(mutex_locked) mtx ∗ P ∗ Φ b }}}
    }}}
      condition_wait_while cond t mtx
    {{{
      RET #();
      mutex.(mutex_locked) mtx ∗ P ∗ Φ false
    }}}.
  Proof.
    iIntros "%Ψ (#Hinv_t & #Hinv_mtx & Hlocked & HP & HΦ & #Hcond) HΨ".
    wp_apply (condition_wait_until_spec _ _ _ P (λ b, Φ (negb b)) with "[$Hlocked $HP $HΦ]"); last done.
    iFrame "#". clear. iIntros "%Ψ !> (Hlocked & HP & HΦ) HΨ".
    wp_pures.
    wp_apply ("Hcond" with "[$]"). iIntros "%b (Hlocked & HP & HΦ)".
    destruct b; wp_pures; iApply "HΨ"; iFrame; done.
  Qed.
End condition.

#[global] Opaque condition_wait_until.
#[global] Opaque condition_wait_while.
