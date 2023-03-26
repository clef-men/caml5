From iris.algebra Require Import
  gset.

From caml5 Require Import
  prelude.
From caml5.common Require Import
  tactics.
From caml5.base_logic Require Import
  lib.auth_excl
  lib.auth_nat_max.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.concurrent Require Export
  base.

Class CounterG Σ `{!heapGS Σ} := {
  counter_G_mono_G : AuthNatMaxG Σ ;
  counter_G_token_G : inG Σ (authR (gset_disjUR nat)) ;
  counter_G_model_G : AuthExclG Σ natO ;
}.
#[local] Existing Instance counter_G_mono_G.
#[local] Existing Instance counter_G_token_G.
#[local] Existing Instance counter_G_model_G.

Definition counter_Σ := #[
  auth_nat_max_Σ ;
  GFunctor (authR (gset_disjUR nat)) ;
  auth_excl_Σ natO
].
Lemma subG_counter_Σ Σ `{!heapGS Σ} :
  subG counter_Σ Σ →
  CounterG Σ.
Proof.
  solve_inG.
Qed.

Section counter_G.
  Context `{CounterG Σ}.
  Implicit Types n m lb : nat.
  Implicit Types l : loc.
  Implicit Types t : val.

  Definition counter_make : val :=
    λ: <>,
      ref #0.
  Definition counter_incr : val :=
    λ: "t",
      FAA "t" #1.
  Definition counter_get : val :=
    λ: "t",
      !"t".

  Notation counter_meta_mono :=
    (nroot .@ "mono").
  Notation counter_meta_token :=
    (nroot .@ "token").
  Notation counter_meta_model :=
    (nroot .@ "model").

  #[local] Definition counter_mono_auth γ_mono dq n :=
    auth_nat_max_auth γ_mono dq n.
  #[local] Definition counter_mono_frag γ_mono n :=
    auth_nat_max_frag γ_mono n.
  Definition counter_lb t lb : iProp Σ :=
    ∃ l γ_mono,
    ⌜t = #l⌝ ∗
    meta l counter_meta_mono γ_mono ∗
    counter_mono_frag γ_mono lb.

  #[local] Definition counter_token_auth γ_token dq n :=
    own γ_token (●{dq} GSet (set_seq 0 n)).
  #[local] Definition counter_token_frag γ_token n :=
    own γ_token (◯ GSet {[n]}).
  Definition counter_token t n : iProp Σ :=
    ∃ l γ_token,
    ⌜t = #l⌝ ∗
    meta l counter_meta_token γ_token ∗
    counter_token_frag γ_token n.

  #[local] Definition counter_model₁ γ_model n :=
    auth_excl_frag γ_model n.
  #[local] Definition counter_model₂ γ_model dq n :=
    auth_excl_auth γ_model dq n.
  Definition counter_model t dq n : iProp Σ :=
    ∃ l γ_mono γ_token γ_model,
    ⌜t = #l⌝ ∗
    meta l counter_meta_mono γ_mono ∗
    meta l counter_meta_token γ_token ∗
    meta l counter_meta_model γ_model ∗
    counter_mono_auth γ_mono dq n ∗
    counter_token_auth γ_token dq n ∗
    counter_model₂ γ_model dq n.

  #[local] Definition counter_inv_inner l γ_model : iProp Σ :=
    ∃ n,
    l ↦ #n ∗
    counter_model₁ γ_model n.
  Definition counter_inv t ι : iProp Σ :=
    ∃ l γ_model,
    ⌜t = #l⌝ ∗
    meta l counter_meta_model γ_model ∗
    inv ι (counter_inv_inner l γ_model).

  #[global] Instance counter_lb_persistent t lb :
    Persistent (counter_lb t lb).
  Proof.
    apply _.
  Qed.
  #[global] Instance counter_token_timeless t n :
    Timeless (counter_token t n).
  Proof.
    apply _.
  Qed.
  #[global] Instance counter_model_timeless t dq n :
    Timeless (counter_model t dq n).
  Proof.
    apply _.
  Qed.
  #[global] Instance counter_model_persistent t n :
    Persistent (counter_model t DfracDiscarded n).
  Proof.
    apply _.
  Qed.
  #[global] Instance counter_inv_persistent t ι :
    Persistent (counter_inv t ι).
  Proof.
    apply _.
  Qed.

  #[global] Instance counter_model_fractional t n :
    Fractional (λ q, counter_model t (DfracOwn q) n).
  Proof.
    intros q1 q2. iSplit.
    - iIntros "(%l & %γ_mono & %γ_token & %γ_model & -> & #Hmeta_mono & #Hmeta_token & #Hmeta_model & (Hmono_auth1 & Hmono_auth2) & (Htoken_auth1 & Htoken_auth2) & (Hmodel₂1 & Hmodel₂2))".
      iSplitL "Hmono_auth1 Htoken_auth1 Hmodel₂1"; repeat iExists _; auto with iFrame.
    - iIntros "((%_l & %_γ_mono & %_γ_token & %_γ_model & % & #Hmeta_mono & #Hmeta_token & #Hmeta_model & Hmono_auth1 & Htoken_auth1 & Hmodel₂1) & (%l & %γ_mono & %γ_token & %γ_model & % & #_Hmeta_mono & #_Hmeta_token & #_Hmeta_model & Hmono_auth2 & Htoken_auth2 & Hmodel₂2))". simplify.
      iDestruct (meta_agree with "Hmeta_mono _Hmeta_mono") as %->. iClear "_Hmeta_mono".
      iDestruct (meta_agree with "Hmeta_token _Hmeta_token") as %->. iClear "_Hmeta_token".
      iDestruct (meta_agree with "Hmeta_model _Hmeta_model") as %->. iClear "_Hmeta_model".
      iCombine "Hmono_auth1 Hmono_auth2" as "Hmono_auth".
      iCombine "Htoken_auth1 Htoken_auth2" as "Htoken_auth".
      iCombine "Hmodel₂1 Hmodel₂2" as "Hmodel₂".
      repeat iExists _. auto with iFrame.
  Qed.
  #[global] Instance counter_model_as_fractional t q n :
    AsFractional (counter_model t (DfracOwn q) n) (λ q, counter_model t (DfracOwn q) n) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma counter_lb_valid t dq n lb :
    counter_model t dq n -∗
    counter_lb t lb -∗
    ⌜lb ≤ n⌝.
  Proof.
    iIntros "(%_l & %_γ_mono & %γ_token & %γ_model & % & #Hmeta_mono & #Hmeta_token & #Hmeta_model & Hmono_auth & Htoken_auth & Hmodel₂) (%l & %γ_mono & % & #_Hmeta_mono & Hmono_frag)". simplify.
    iDestruct (meta_agree with "Hmeta_mono _Hmeta_mono") as %->. iClear "_Hmeta_mono".
    iApply (auth_nat_max_valid with "Hmono_auth Hmono_frag").
  Qed.
  Lemma counter_lb_le t lb1 lb2 :
    lb2 ≤ lb1 →
    counter_lb t lb1 -∗
    counter_lb t lb2.
  Proof.
    iIntros "% (%l & %γ_mono & -> & #Hmeta_mono & Hmono_frag)".
    iDestruct (auth_nat_max_frag_le with "Hmono_frag") as "Hmono_frag"; first done.
    repeat iExists _. naive_solver.
  Qed.
  Lemma counter_lb_get t dq n :
    counter_model t dq n -∗
    counter_lb t n.
  Proof.
    iIntros "(%l & %γ_mono & %γ_token & %γ_model & % & #Hmeta_mono & #Hmeta_token & #Hmeta_model & Hmono_auth & Htoken_auth & Hmodel₂)".
    iDestruct (auth_nat_max_frag_get with "Hmono_auth") as "#Hmono_frag".
    repeat iExists _. naive_solver.
  Qed.

  Lemma counter_token_valid t dq n m :
    counter_model t dq n -∗
    counter_token t m -∗
    ⌜m < n⌝.
  Proof.
    iIntros "(%_l & %γ_mono & %_γ_token & %γ_model & % & #Hmeta_mono & #Hmeta_token & #Hmeta_model & Hmono_auth & Htoken_auth & Hmodel₂) (%l & %γ_token & % & #_Hmeta_token & Htoken_frag)". simplify.
    iDestruct (meta_agree with "Hmeta_token _Hmeta_token") as %->. iClear "_Hmeta_token".
    iDestruct (own_valid_2 with "Htoken_auth Htoken_frag") as %(_ & Hincluded & _)%auth_both_dfrac_valid_discrete.
    rewrite gset_disj_included -elem_of_subseteq_singleton elem_of_set_seq in Hincluded.
    naive_solver.
  Qed.
  Lemma counter_token_exclusive t n :
    counter_token t n -∗
    counter_token t n -∗
    False.
  Proof.
    iIntros "(%_l & %_γ_token & % & #Hmeta_token & Htoken_frag1) (%l & %γ_token & % & #_Hmeta_token & Htoken_frag2)". simplify.
    iDestruct (meta_agree with "Hmeta_token _Hmeta_token") as %->. iClear "_Hmeta_token".
    iDestruct (own_valid_2 with "Htoken_frag1 Htoken_frag2") as %?%auth_frag_op_valid%gset_disj_valid_op.
    set_solver.
  Qed.

  Lemma counter_model_persist t dq n :
    counter_model t dq n ==∗
    counter_model t DfracDiscarded n.
  Proof.
    iIntros "(%l & %γ_mono & %γ_token & %γ_model & -> & #Hmeta_mono & #Hmeta_token & #Hmeta_model & Hmono_auth & Htoken_auth & Hmodel₂)".
    iMod (auth_nat_max_auth_persist with "Hmono_auth") as "Hmono_auth".
    iMod (own_update with "Htoken_auth") as "Htoken_auth"; first eapply auth_update_auth_persist.
    iMod (auth_excl_auth_persist with "Hmodel₂") as "Hmodel₂".
    repeat iExists _. iFrame "∗#". done.
  Qed.
  Lemma counter_model_valid t dq n :
    counter_model t dq n -∗
    ⌜✓ dq⌝.
  Proof.
    iIntros "(%l & %γ_mono & %γ_token & %γ_model & -> & #Hmeta_mono & #Hmeta_token & #Hmeta_model & Hmono_auth & Htoken_auth & Hmodel₂)".
    iApply (auth_excl_auth_valid with "Hmodel₂").
  Qed.
  Lemma counter_model_combine t dq1 n1 dq2 n2 :
    counter_model t dq1 n1 -∗
    counter_model t dq2 n2 -∗
      counter_model t (dq1 ⋅ dq2) n1 ∗
      ⌜n1 = n2⌝.
  Proof.
    iIntros "(%_l & %_γ_mono & %_γ_token & %_γ_model & % & #Hmeta_mono & #Hmeta_token & #Hmeta_model & Hmono_auth1 & Htoken_auth1 & Hmodel₂1) (%l & %γ_mono & %γ_token & %γ_model & % & #_Hmeta_mono & #_Hmeta_token & #_Hmeta_model & Hmono_auth2 & Htoken_auth2 & Hmodel₂2)". simplify.
    iDestruct (meta_agree with "Hmeta_mono _Hmeta_mono") as %->. iClear "_Hmeta_mono".
    iDestruct (meta_agree with "Hmeta_token _Hmeta_token") as %->. iClear "_Hmeta_token".
    iDestruct (meta_agree with "Hmeta_model _Hmeta_model") as %->. iClear "_Hmeta_model".
    iDestruct (auth_nat_max_auth_combine with "Hmono_auth1 Hmono_auth2") as "(Hmono_auth & <-)".
    iCombine "Htoken_auth1 Htoken_auth2" as "Htoken_auth".
    iDestruct (auth_excl_auth_combine_L with "Hmodel₂1 Hmodel₂2") as "(Hmodel₂ & _)".
    iSplitL; last done. repeat iExists _. iFrame "∗#". done.
  Qed.
  Lemma counter_model_valid_2 t dq1 n1 dq2 n2 :
    counter_model t dq1 n1 -∗
    counter_model t dq2 n2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ n1 = n2⌝.
  Proof.
    iIntros "Hmodel1 Hmodel2".
    iDestruct (counter_model_combine with "Hmodel1 Hmodel2") as "(Hmodel & %)".
    iDestruct (counter_model_valid with "Hmodel") as %?.
    done.
  Qed.
  Lemma counter_model_agree t dq1 n1 dq2 n2 :
    counter_model t dq1 n1 -∗
    counter_model t dq2 n2 -∗
    ⌜n1 = n2⌝.
  Proof.
    iIntros "Hmodel1 Hmodel2".
    iDestruct (counter_model_combine with "Hmodel1 Hmodel2") as "(_ & <-)"; done.
  Qed.
  Lemma counter_model_dfrac_ne t1 dq1 n1 t2 dq2 n2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    counter_model t1 dq1 n1 -∗
    counter_model t2 dq2 n2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    iIntros "% Hmodel1 Hmodel2" (->).
    iDestruct (counter_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
  Qed.
  Lemma counter_model_ne t1 n1 t2 dq2 n2 :
    counter_model t1 (DfracOwn 1) n1 -∗
    counter_model t2 dq2 n2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    intros. iApply counter_model_dfrac_ne. intros []%exclusive_l. apply _.
  Qed.
  Lemma counter_model_exclusive t n1 n2 :
    counter_model t (DfracOwn 1) n1 -∗
    counter_model t (DfracOwn 1) n2 -∗
    False.
  Proof.
    iIntros "Hmodel1 Hmodel2".
    iDestruct (counter_model_ne with "Hmodel1 Hmodel2") as %?; naive_solver.
  Qed.

  Lemma counter_make_spec ι :
    {{{ True }}}
      counter_make #()
    {{{ t, RET t; counter_inv t ι ∗ counter_model t (DfracOwn 1) 0 }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec. iApply wp_fupd. wp_apply (wp_alloc with "[//]"). iIntros "%l (Hl & Hmeta)".
    iMod (auth_nat_max_alloc 0) as "(%γ_mono & Hmono_auth & _)".
    iMod (own_alloc (● GSet ∅)) as "(%γ_token & Htoken_auth)"; first by apply auth_auth_valid.
    iMod (auth_excl_alloc 0) as "(%γ_model & Hmodel₂ & Hmodel₁)"; first done.
    iDestruct (meta_token_difference _ (↑counter_meta_mono) with "Hmeta") as "(Hmeta_mono & Hmeta)"; first solve_ndisj.
    iDestruct (meta_token_difference _ (↑counter_meta_token) with "Hmeta") as "(Hmeta_token & Hmeta)"; first solve_ndisj.
    iDestruct (meta_token_difference _ (↑counter_meta_model) with "Hmeta") as "(Hmeta_model & Hmeta)"; first solve_ndisj.
    iMod (meta_set _ _ γ_mono with "Hmeta_mono") as "#Hmeta_mono"; first done.
    iMod (meta_set _ _ γ_token with "Hmeta_token") as "#Hmeta_token"; first done.
    iMod (meta_set _ _ γ_model with "Hmeta_model") as "#Hmeta_model"; first done.
    iApply "HΦ". iSplitL "Hl Hmodel₁".
    - iExists l, γ_model. repeat iSplitR; [done.. |].
      iApply inv_alloc. iExists 0. iFrame.
    - iExists l, γ_mono, γ_token, γ_model. iFrame "∗#". done.
  Qed.

  Lemma counter_incr_spec t ι :
    <<< counter_inv t ι | ∀∀ n, counter_model t (DfracOwn 1) n >>>
      counter_incr t @ ↑ι
    <<< counter_model t (DfracOwn 1) (S n) ∗ counter_token t n | RET #n; True >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ_model & -> & #Hmeta_model & #Hinv) HΦ".
    wp_rec.
    iInv "Hinv" as "(%n & Hl & Hmodel₁)".
    wp_faa.
    iMod "HΦ" as "(%_n & (%_l & %γ_mono & %γ_token & %_γ_model & %Heq & #Hmeta_mono & #Hmeta_token & #_Hmeta_model & Hmono_auth & Htoken_auth & Hmodel₂) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta_model _Hmeta_model") as %<-. iClear "_Hmeta_model".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iMod (auth_nat_max_update (S n) with "Hmono_auth") as "Hmono_auth"; first lia.
    iMod (own_update _ _ (● GSet (set_seq 0 (S n)) ⋅ ◯ GSet {[n]}) with "Htoken_auth") as "(Htoken_auth & Htoken_frag)".
    { apply auth_update_alloc.
      rewrite set_seq_S_end_union_L. apply gset_disj_alloc_empty_local_update.
      rewrite -{1}(Nat.add_0_l n). apply set_seq_S_end_disjoint.
    }
    iMod (auth_excl_update' (S n) with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
    iAssert (counter_token #l n) with "[Htoken_frag]" as "Htoken".
    { iExists l, γ_token. naive_solver. }
    iAssert (counter_model #l (DfracOwn 1) (S n)) with "[Hmono_auth Htoken_auth Hmodel₂]" as "Hmodel".
    { iExists l, γ_mono, γ_token, γ_model. iFrame "∗#". done. }
    iMod ("HΦ" with "[$Hmodel $Htoken] [//]") as "$".
    iModIntro. iExists (S n). iNext. iFrame.
    assert (n + 1 = S n)%Z as -> by lia. done.
  Qed.

  Lemma counter_get_spec t ι :
    <<< counter_inv t ι | ∀∀ dq n, counter_model t dq n >>>
      counter_get t @ ↑ι
    <<< counter_model t dq n | RET #n; True >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ_model & -> & #Hmeta_model & #Hinv) HΦ".
    wp_rec.
    iInv "Hinv" as "(%n & Hl & Hmodel₁)".
    wp_load.
    iMod "HΦ" as "(%dq & %_n & (%_l & %γ_mono & %γ_token & %_γ_model & %Heq & #Hmeta_mono & #Hmeta_token & #_Hmeta_model & Hmono_auth & Htoken_auth & Hmodel₂) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta_model _Hmeta_model") as %<-. iClear "_Hmeta_model".
    iDestruct (auth_excl_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iAssert (counter_model #l dq n) with "[Hmono_auth Htoken_auth Hmodel₂]" as "Hmodel".
    { iExists l, γ_mono, γ_token, γ_model. iFrame "∗#". done. }
    iMod ("HΦ" with "Hmodel [//]") as "$".
    iModIntro. iNext. iExists n. iFrame.
  Qed.

  Lemma counter_unboxed t ι :
    counter_inv t ι -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "(%l & %γ_model & -> & #Hmeta_model & #Hinv) //".
  Qed.
End counter_G.

#[global] Opaque counter_make.
#[global] Opaque counter_incr.
#[global] Opaque counter_get.

#[global] Opaque counter_lb.
#[global] Opaque counter_token.
#[global] Opaque counter_model.
#[global] Opaque counter_inv.
