From Coq.Logic Require Import
  FunctionalExtensionality.

From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations.
From caml5.std Require Export
  base.

Implicit Types t v : val.
Implicit Types i : Z.

Record inf_array `{!heapGS Σ} := {
  inf_array_make : val ;
  inf_array_get : val ;
  inf_array_set : val ;

  inf_array_model : val → (nat → val) → iProp Σ ;

  inf_array_model_timeless t vs :
    Timeless (inf_array_model t vs) ;

  inf_array_make_spec v :
    {{{ True }}}
      inf_array_make v
    {{{ t, RET t; inf_array_model t (λ _, v) }}} ;

  inf_array_get_spec t i :
    (0 ≤ i)%Z →
    <<< True | ∀∀ vs, inf_array_model t vs >>>
      inf_array_get t #i
    <<< inf_array_model t vs | RET vs (Z.to_nat i); True >>> ;

  inf_array_set_spec t i v :
    (0 ≤ i)%Z →
    <<< True | ∀∀ vs, inf_array_model t vs >>>
      inf_array_set t #i v
    <<< inf_array_model t (<[Z.to_nat i := v]> vs) | RET #(); True >>> ;
}.
#[global] Arguments inf_array _ {_} : assert.
#[global] Arguments Build_inf_array {_ _ _ _ _ _ _} _ _ _ : assert.
#[global] Existing Instance inf_array_model_timeless.

Section inf_array.
  Context `{!heapGS Σ} (inf_array : inf_array Σ).

  #[global] Instance inf_array_model_ne t n :
    Proper ((pointwise_relation nat (=)) ==> (≡{n}≡)) (inf_array.(inf_array_model) t).
  Proof.
    intros vs1 vs2 ->%functional_extensionality. done.
  Qed.
  #[global] Instance inf_array_model_proper t :
    Proper ((pointwise_relation nat (=)) ==> (≡)) (inf_array.(inf_array_model) t).
  Proof.
    intros vs1 vs2 Hvs. rewrite equiv_dist. solve_proper.
  Qed.
End inf_array.
