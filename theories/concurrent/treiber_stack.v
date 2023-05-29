From caml5 Require Import
  prelude.
From caml5.base_logic Require Import
  lib.auth_excl.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Import
  mlst.
From caml5.concurrent Require Export
  base.
From caml5.concurrent Require Import
  mpmc_stack.

Class TreiberG Σ `{!heapGS Σ} := {
  #[local] treiber_stack_G_model_G :: AuthExclG Σ (leibnizO (list val)) ;
}.

Definition treiber_stack_Σ := #[
  auth_excl_Σ (leibnizO (list val))
].
#[global] Instance subG_treiber_stack_Σ Σ `{!heapGS Σ} :
  subG treiber_stack_Σ Σ →
  TreiberG Σ.
Proof.
  solve_inG.
Qed.

Section treiber_stack_G.
  Context `{treiber_G : TreiberG Σ}.
  Implicit Types l : loc.
  Implicit Types v t lst : val.

  Definition treiber_stack_make : val :=
    λ: <>,
      ref mlst_nil.

  Definition treiber_stack_push : val :=
    rec: "treiber_stack_push" "t" "v" :=
      let: "old_contents" := !"t" in
      if: CAS "t" "old_contents" (mlst_cons "v" "old_contents") then (
        #()
      ) else (
        "treiber_stack_push" "t" "v"
      ).

  Definition treiber_stack_pop : val :=
    rec: "treiber_stack_pop" "t" :=
      let: "old_contents" := !"t" in
      if: mlst_is_empty "old_contents" then (
        NONE
      ) else (
        let: "v" := mlst_head "old_contents" in
        let: "contents" := mlst_tail "old_contents" in
        if: CAS "t" "old_contents" "contents" then (
          SOME "v"
        ) else (
          "treiber_stack_pop" "t"
        )
      ).

  #[local] Definition treiber_name := gname.
  Implicit Types γ : treiber_name.

  #[local] Definition treiber_stack_model₁ γ vs : iProp Σ :=
    auth_excl_frag γ vs.
  #[local] Definition treiber_stack_model₂ γ vs : iProp Σ :=
    auth_excl_auth γ (DfracOwn 1) vs.

  Definition treiber_stack_inv_inner t l γ : iProp Σ :=
    ∃ lst vs,
    l ↦ lst ∗ mlst_model lst DfracDiscarded vs ∗ treiber_stack_model₁ γ vs.
  Definition treiber_stack_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv ι (treiber_stack_inv_inner t l γ).

  Definition treiber_stack_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    treiber_stack_model₂ γ vs.

  #[global] Instance treiber_stack_inv_persistent t ι :
    Persistent (treiber_stack_inv t ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance treiber_stack_model_timeless t vs :
    Timeless (treiber_stack_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma treiber_stack_make_spec ι :
    {{{ True }}}
      treiber_stack_make #()
    {{{ t,
      RET t;
      treiber_stack_inv t ι ∗
      treiber_stack_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    iApply wp_fupd. wp_apply (wp_alloc with "[//]"). iIntros "%l (Hl & Hmeta)".
    iApply "HΦ".
    iMod (auth_excl_alloc' (auth_excl_G := treiber_stack_G_model_G) []) as "(%γ & Hmodel₂ & Hmodel₁)".
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.
    iSplitR "Hmodel₂"; iExists l, γ; iFrame "∗#"; last done.
    iSplitR; first done. iApply inv_alloc. iNext. iExists mlst_nil, []. iFrame "∗#".
    iApply mlst_nil_spec.
  Qed.

  Lemma treiber_stack_push_spec t ι v :
    <<<
      treiber_stack_inv t ι
    | ∀∀ vs, treiber_stack_model t vs
    >>>
      treiber_stack_push t v @ ↑ι
    <<<
      treiber_stack_model t (v :: vs)
    | RET #(); True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".
    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (! _)%E.
    iInv "Hinv" as "(%lst1 & %vs1 & Hl & #Hlst1 & Hmodel₁)".
    wp_load.
    iModIntro. iSplitL "Hl Hmodel₁".
    { iExists lst1, vs1. auto with iFrame. }

    wp_pures.
    wp_apply (mlst_cons_spec with "Hlst1"); first done. iIntros "%lst1' #Hlst1'".

    wp_bind (CmpXchg _ _ _).
    iInv "Hinv" as "(%lst2 & %vs2 & Hl & >#Hlst2 & Hmodel₁)".
    iDestruct (mlst_unboxed with "Hlst1") as %?. wp_cmpxchg as -> | ?.

    - iDestruct (mlst_model_agree with "Hlst1 Hlst2") as %<-.
      iMod "HΦ" as "(%_vs1 & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₂) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
      iMod (auth_excl_update' (auth_excl_G := treiber_stack_G_model_G) (v :: vs1) with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
      iMod ("HΦ" with "[Hmodel₂] [//]") as "HΦ".
      { iExists l, γ. auto with iFrame. }
      iModIntro. iSplitL "Hl Hmodel₁".
      { iExists lst1', (v :: vs1). auto with iFrame. }

      wp_pures.

      iApply "HΦ".

    - iModIntro. iSplitL "Hl Hmodel₁".
      { iExists lst2, vs2. auto with iFrame. }

      wp_pures.

      wp_apply ("HLöb" with "HΦ").
  Qed.

  Lemma treiber_stack_pop_spec t ι :
    <<<
      treiber_stack_inv t ι
    | ∀∀ vs, treiber_stack_model t vs
    >>>
      treiber_stack_pop t @ ↑ι
    <<< ∃∃ o,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          treiber_stack_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          treiber_stack_model t vs'
      end
    | RET o; True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".
    iLöb as "HLöb".

    wp_rec.

    wp_bind (! _)%E.
    iInv "Hinv" as "(%lst1 & %vs1 & Hl & #Hlst1 & Hmodel₁)".
    wp_load.
    destruct vs1 as [| v1 vs1].

    - iMod "HΦ" as "(%_vs1 & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₂) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
      iMod ("HΦ" $! None with "[Hmodel₂] [//]") as "HΦ".
      { iSplit; first done. iExists l, γ. auto. }
      iModIntro. iSplitL "Hl Hmodel₁".
      { iExists lst1, []. auto with iFrame. }

      wp_pures.

      wp_apply (mlst_is_empty_spec with "Hlst1"). iIntros "_".

      wp_pures.

      iApply "HΦ".

    - iModIntro. iSplitL "Hl Hmodel₁".
      { iExists lst1, (v1 :: vs1). auto with iFrame. }

      wp_pures.

      wp_apply (mlst_is_empty_spec with "Hlst1"). iIntros "_".

      wp_pures.

      wp_apply (mlst_head_spec with "Hlst1"). iIntros "_".

      wp_pures.

      wp_apply (mlst_tail_spec with "Hlst1"). iIntros "%lst1' (_ & #Hlst1')".

      wp_pures.

      wp_bind (CmpXchg _ _ _).
      iInv "Hinv" as "(%lst2 & %vs2 & Hl & >#Hlst2 & Hmodel₁)".
      iDestruct (mlst_unboxed with "Hlst1") as %?. wp_cmpxchg as -> | ?.

      + iDestruct (mlst_model_agree with "Hlst1 Hlst2") as %<-.
        iMod "HΦ" as "(%_vs1 & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₂) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
        iMod (auth_excl_update' (auth_excl_G := treiber_stack_G_model_G) vs1 with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
        iMod ("HΦ" $! (Some v1) with "[Hmodel₂] [//]") as "HΦ".
        { iExists vs1. iSplit; first done. iExists l, γ. auto. }
        iModIntro. iSplitL "Hl Hmodel₁".
        { iExists lst1', vs1. auto with iFrame. }

        wp_pures.

        iApply "HΦ".

      + iModIntro. iSplitL "Hl Hmodel₁".
        { iExists lst2, vs2. auto with iFrame. }

        wp_pures.

        wp_apply ("HLöb" with "HΦ").
  Qed.

  Lemma treiber_stack_unboxed t ι :
    treiber_stack_inv t ι -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & #Hinv) //".
  Qed.

  Program Definition treiber_mpmc_stack : mpmc_stack Σ true := {|
    mpmc_stack_make := treiber_stack_make ;
    mpmc_stack_push := treiber_stack_push ;
    mpmc_stack_pop := treiber_stack_pop ;

    mpmc_stack_name := unit ;
    mpmc_stack_inv t _ ι := treiber_stack_inv t ι ;
    mpmc_stack_model t _ vs := treiber_stack_model t vs ;
  |}.
  Next Obligation.
    intros. iIntros "_ HΦ".
    wp_apply (treiber_stack_make_spec with "[//]"). iIntros "%t".
    iApply ("HΦ" $! t ()).
  Qed.
  Next Obligation.
    intros. iApply treiber_stack_push_spec.
  Qed.
  Next Obligation.
    intros. iApply treiber_stack_pop_spec.
  Qed.
  Next Obligation.
    simpl. intros. iApply treiber_stack_unboxed.
  Qed.
End treiber_stack_G.

#[global] Opaque treiber_stack_make.
#[global] Opaque treiber_stack_push.
#[global] Opaque treiber_stack_pop.

#[global] Opaque treiber_stack_inv.
#[global] Opaque treiber_stack_model.
