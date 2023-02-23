From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.

Implicit Types t : val.

Record mutex `{!heapGS Σ} := {
  mutex_make : val ;
  mutex_lock : val ;
  mutex_unlock : val ;

  mutex_inv : val → iProp Σ → iProp Σ ;
  mutex_locked : val → iProp Σ ;

  mutex_inv_ne t :
    NonExpansive (mutex_inv t) ;
  mutex_inv_proper t :
    Proper ((≡) ==> (≡)) (mutex_inv t) ;

  mutex_inv_persistent t P :
    Persistent (mutex_inv t P) ;
  mutex_locked_timeless t :
    Timeless (mutex_locked t) ;

  mutex_locked_exclusive t :
    mutex_locked t -∗
    mutex_locked t -∗
    False ;

  mutex_make_spec P :
    {{{ P }}}
      mutex_make #()
    {{{ t, RET t; mutex_inv t P }}} ;

  mutex_lock_spec t P :
    {{{ mutex_inv t P }}}
      mutex_lock t
    {{{ RET #(); mutex_locked t ∗ P }}} ;

  mutex_unlock_spec t P :
    {{{ mutex_inv t P ∗ mutex_locked t ∗ P }}}
      mutex_unlock t
    {{{ RET #(); True }}} ;
}.
#[global] Arguments mutex _ {_} : assert.
#[global] Arguments Build_mutex {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _ : assert.
#[global] Existing Instance mutex_inv_ne.
#[global] Existing Instance mutex_inv_proper.
#[global] Existing Instance mutex_inv_persistent.
#[global] Existing Instance mutex_locked_timeless.

Section mutex.
  Context `{!heapGS Σ} (mutex : mutex Σ).

  Definition mutex_protect : val :=
    λ: "t" "fn",
      mutex.(mutex_lock) "t" ;;
      let: "res" := "fn" #() in
      mutex.(mutex_unlock) "t" ;;
      "res".

  Lemma mutex_protect_spec t P (fn : val) Φ :
    {{{ mutex.(mutex_inv) t P ∗ {{{ P }}} fn #() {{{ v, RET v; P ∗ Φ v }}} }}}
      mutex_protect t fn
    {{{ v, RET v; Φ v }}}.
  Proof.
    iIntros "%Ψ (#Hinv & Hfn) HΨ".
    wp_rec. wp_pures.
    wp_apply (mutex_lock_spec with "Hinv"). iIntros "(Hlocked & HP)".
    wp_pures.
    wp_apply ("Hfn" with "HP"). iIntros "%v (HP & HΦ)".
    wp_pures.
    wp_apply (mutex_unlock_spec with "[$Hinv $Hlocked $HP]"). iIntros "_".
    wp_pures.
    iApply "HΨ". done.
  Qed.
End mutex.

#[global] Opaque mutex_protect.
