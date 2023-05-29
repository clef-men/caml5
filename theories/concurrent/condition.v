From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.concurrent Require Export
  mutex.

Record condition `{!heapGS Σ} {mutex_unboxed} {mutex : mutex Σ mutex_unboxed} {unboxed : bool} := {
  condition_make : val ;
  condition_wait : val ;
  condition_signal : val ;
  condition_broadcast : val ;

  condition_inv : val → iProp Σ ;

  #[global] condition_inv_persistent t ::
    Persistent (condition_inv t) ;

  condition_make_spec :
    {{{ True }}}
      condition_make #()
    {{{ t,
      RET t; condition_inv t
    }}} ;

  condition_wait_spec t mtx P :
    {{{
      condition_inv t ∗
      mutex.(mutex_inv) mtx P ∗
      mutex.(mutex_locked) mtx ∗ P
    }}}
      condition_wait t mtx
    {{{
      RET #();
      mutex.(mutex_locked) mtx ∗ P
    }}} ;

  condition_signal_spec t :
    {{{
      condition_inv t
    }}}
      condition_signal t
    {{{
      RET #(); True
    }}} ;

  condition_broadcast_spec t :
    {{{
      condition_inv t
    }}}
      condition_broadcast t
    {{{
      RET #(); True
    }}} ;

  condition_unboxed :
    if unboxed then ∀ t,
      condition_inv t -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments condition _ {_ _} _ _ : assert.
#[global] Arguments Build_condition {_ _ _ _} _ {_ _ _ _ _ _} _ _ _ _ _ : assert.

Section condition.
  Context `{!heapGS Σ}.
  Context {mutex_unboxed} {mutex : mutex Σ mutex_unboxed}.
  Context {unboxed} (condition : condition Σ mutex unboxed).
  Implicit Types cond : val.

  #[local] Definition condition_wait_until_aux : val :=
    rec: "condition_wait_until_aux" "t" "mtx" "cond" :=
      if: "cond" #() then #() else (
        condition.(condition_wait) "t" "mtx" ;;
        "condition_wait_until_aux" "t" "mtx" "cond"
      ).
  Definition condition_wait_until : val :=
    λ: "t" "mtx" "cond",
      condition_wait_until_aux "t" "mtx" "cond".

  Definition condition_wait_while : val :=
    λ: "t" "mtx" "cond",
      condition_wait_until "t" "mtx" (λ: <>, ~ "cond" #()).

  Lemma condition_wait_until_spec Ψ t mtx cond P :
    {{{
      condition.(condition_inv) t ∗
      mutex.(mutex_inv) mtx P ∗
      mutex.(mutex_locked) mtx ∗ P ∗
      Ψ false ∗
      {{{
        mutex.(mutex_locked) mtx ∗ P ∗
        Ψ false
      }}}
        cond #()
      {{{ (b : bool),
        RET #b;
        mutex.(mutex_locked) mtx ∗ P ∗
        Ψ b
      }}}
    }}}
      condition_wait_until t mtx cond
    {{{
      RET #();
      mutex.(mutex_locked) mtx ∗ P ∗
      Ψ true
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hlocked & HP & HΨ & #Hcond) HΦ".
    wp_rec. wp_pures.
    iLöb as "HLöb".
    wp_rec.
    wp_smart_apply ("Hcond" with "[$]"). iIntros "%b (Hlocked & HP & HΨ)".
    destruct b; wp_pures.
    { iApply "HΦ". iFrame. done. }
    wp_apply (condition_wait_spec _ _ _ P with "[$]"). iIntros "(Hlocked & HP)".
    wp_pures.
    iApply ("HLöb" with "Hlocked HP HΨ HΦ").
  Qed.

  Lemma condition_wait_while_spec Ψ t mtx cond P :
    {{{
      condition.(condition_inv) t ∗
      mutex.(mutex_inv) mtx P ∗
      mutex.(mutex_locked) mtx ∗ P ∗
      Ψ true ∗
      {{{
        mutex.(mutex_locked) mtx ∗ P ∗
        Ψ true
      }}}
        cond #()
      {{{ (b : bool),
        RET #b;
        mutex.(mutex_locked) mtx ∗ P ∗
        Ψ b
      }}}
    }}}
      condition_wait_while t mtx cond
    {{{
      RET #();
      mutex.(mutex_locked) mtx ∗ P ∗
      Ψ false
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hlocked & HP & HΨ & #Hcond) HΦ".
    wp_rec.
    wp_smart_apply (condition_wait_until_spec (λ b, Ψ (negb b)) _ _ _ P with "[$Hlocked $HP $HΨ]"); last done.
    iFrame "#∗". clear. iIntros "%Φ !> (Hlocked & HP & HΨ) HΦ".
    wp_smart_apply ("Hcond" with "[$]"). iIntros "%b (Hlocked & HP & HΨ)".
    destruct b; wp_pures; iApply "HΦ"; iFrame; done.
  Qed.
End condition.

#[global] Opaque condition_wait_until.
#[global] Opaque condition_wait_while.

Notation "condition .(condition_wait_until)" := (condition_wait_until condition)
( at level 5
).
Notation "condition .(condition_wait_while)" := (condition_wait_while condition)
( at level 5
).
