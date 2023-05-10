From Coq.Logic Require Import
  FunctionalExtensionality.

From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  base.

Implicit Types t v : val.

Record inf_array `{!heapGS Σ} {unboxed : bool} := {
  inf_array_make : val ;
  inf_array_get : val ;
  inf_array_set : val ;

  inf_array_model : val → (nat → val) → iProp Σ ;

  inf_array_model_timeless t vs :
    Timeless (inf_array_model t vs) ;

  inf_array_make_spec v :
    {{{ True }}}
      inf_array_make v
    {{{ t,
      RET t;
      inf_array_model t (λ _, v)
    }}} ;

  inf_array_get_spec t i :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ vs, inf_array_model t vs
    >>>
      inf_array_get t #i
    <<<
      inf_array_model t vs
    | RET vs (Z.to_nat i); True
    >>> ;

  inf_array_set_spec t i v :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ vs, inf_array_model t vs
    >>>
      inf_array_set t #i v
    <<<
      inf_array_model t (<[Z.to_nat i := v]> vs)
    | RET #(); True
    >>> ;

  inf_array_unboxed :
    if unboxed then ∀ t vs,
      inf_array_model t vs -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments inf_array _ {_} _ : assert.
#[global] Arguments Build_inf_array {_ _} _ {_ _ _ _ _} _ _ _ _ : assert.
#[global] Existing Instance inf_array_model_timeless.

Section inf_array.
  Context `{!heapGS Σ} {unboxed} (inf_array : inf_array Σ unboxed).

  #[global] Instance inf_array_model_ne t n :
    Proper (pointwise_relation nat (=) ==> (≡{n}≡)) (inf_array.(inf_array_model) t).
  Proof.
    intros vs1 vs2 ->%functional_extensionality. done.
  Qed.
  #[global] Instance inf_array_model_proper t :
    Proper (pointwise_relation nat (=) ==> (≡)) (inf_array.(inf_array_model) t).
  Proof.
    intros vs1 vs2 Hvs. rewrite equiv_dist. solve_proper.
  Qed.

  Definition inf_array_model' t vsₗ vsᵣ :=
    inf_array.(inf_array_model) t (
      λ i,
        if decide (i < length vsₗ) then vsₗ !!! i else vsᵣ (i - length vsₗ)
    ).

  #[global] Instance inf_array_model'_ne t n :
    Proper ((=) ==> pointwise_relation nat (=) ==> (≡{n}≡)) (inf_array_model' t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance inf_array_model'_proper t :
    Proper ((=) ==> pointwise_relation nat (=) ==> (≡)) (inf_array_model' t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance inf_array_model'_timeless t vsₗ vsᵣ :
    Timeless (inf_array_model' t vsₗ vsᵣ).
  Proof.
    apply _.
  Qed.

  Lemma inf_array_get_spec' i t :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ vsₗ vsᵣ, inf_array_model' t vsₗ vsᵣ
    >>>
      inf_array.(inf_array_get) t #i
    <<<
      inf_array_model' t vsₗ vsᵣ
    | RET
        let i := Z.to_nat i in
        if decide (i < length vsₗ) then vsₗ !!! i else vsᵣ (i - length vsₗ);
      True
    >>>.
  Proof.
    iIntros "% !> %Φ _ HΦ".
    awp_apply (inf_array_get_spec with "[//]"); first done.
    iApply (aacc_aupd with "HΦ"); first done.
    iIntros "%vsₗ %vsᵣ Hmodel". iAaccIntro with "Hmodel"; first auto with iFrame.
    iIntros "$ !>". iRight. iIntros "HΦ !> _". iApply ("HΦ" with "[//]").
  Qed.

  Lemma inf_array_set_spec' i v t :
    (0 ≤ i)%Z →
    <<<
      True
    | ∀∀ vsₗ vsᵣ, inf_array_model' t vsₗ vsᵣ
    >>>
      inf_array.(inf_array_set) t #i v
    <<<
      let i := Z.to_nat i in
      if decide (i < length vsₗ)
      then inf_array_model' t (<[i := v]> vsₗ) vsᵣ
      else inf_array_model' t vsₗ (<[i - length vsₗ := v]> vsᵣ)
    | RET #(); True
    >>>.
  Proof.
    iIntros "% !> %Φ _ HΦ".
    awp_apply (inf_array_set_spec with "[//]"); first done.
    iApply (aacc_aupd with "HΦ"); first done.
    iIntros "%vsₗ %vsᵣ Hmodel". iAaccIntro with "Hmodel"; first auto with iFrame.
    iIntros "Hmodel !>". iRight. iSplitL "Hmodel".
    - generalize (Z.to_nat i). clear. intros i. case_decide.
      all: iApply (inf_array_model_proper with "Hmodel"); intros j.
      + rewrite insert_length. case_decide.
        * destruct (decide (j = i)) as [-> |].
          -- rewrite list_lookup_total_insert // fn_lookup_insert //.
          -- rewrite list_lookup_total_insert_ne // fn_lookup_insert_ne // decide_True //.
        * rewrite fn_lookup_insert_ne; last lia.
          rewrite decide_False //.
      + case_decide.
        * rewrite fn_lookup_insert_ne; last lia.
          rewrite decide_True //.
        * destruct (decide (j = i)) as [-> |].
          -- rewrite !fn_lookup_insert //.
          -- rewrite !fn_lookup_insert_ne; try lia.
             rewrite decide_False //.
    - iIntros "HΦ !> _". iApply ("HΦ" with "[//]").
  Qed.

  Lemma inf_array_model'_shift t vsₗ v vsᵣ :
    inf_array_model' t (vsₗ ++ [v]) vsᵣ ⊣⊢
    inf_array_model' t vsₗ (λ i, match i with 0 => v | S i => vsᵣ i end).
  Proof.
    rewrite /inf_array_model' inf_array_model_proper; first done.
    intros j. rewrite app_length /=.
    destruct (Nat.lt_total j (length vsₗ)) as [| [-> |]].
    - rewrite !decide_True; try lia.
      rewrite lookup_total_app_l //.
    - rewrite decide_True; last lia.
      rewrite decide_False; last lia.
      rewrite lookup_total_app_r //.
      rewrite Nat.sub_diag //.
    - rewrite !decide_False; try lia.
      case_match; [lia | f_equal; lia].
  Qed.
  Lemma inf_array_model'_shift_r t vsₗ v vsᵣ :
    inf_array_model' t (vsₗ ++ [v]) vsᵣ -∗
    inf_array_model' t vsₗ (λ i, match i with 0 => v | S i => vsᵣ i end).
  Proof.
    rewrite inf_array_model'_shift //.
  Qed.
  Lemma inf_array_model'_shift_l t vsₗ vsᵣ v vsᵣ' :
    (∀ i, vsᵣ i = match i with 0 => v | S i => vsᵣ' i end) →
    inf_array_model' t vsₗ vsᵣ -∗
    inf_array_model' t (vsₗ ++ [v]) vsᵣ'.
  Proof.
    intros. rewrite inf_array_model'_shift inf_array_model'_proper //.
  Qed.
End inf_array.

Notation "inf_array .(inf_array_model')" := (inf_array_model' inf_array)
( at level 5
).
