From caml5 Require Import
  prelude.
From caml5.base_logic Require Import
  lib.excl.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.concurrent Require Export
  base.

Class DomainG Σ `{!heapGS Σ} := {
  domain_G_model_G : ExclG Σ unitO ;
}.
#[local] Existing Instance domain_G_model_G.

Definition domain_Σ := #[
  excl_Σ unitO
].
#[global] Instance subG_domain_Σ Σ `{!heapGS Σ} :
  subG domain_Σ Σ →
  DomainG Σ.
Proof.
  solve_inG.
Qed.

Section domain_G.
  Context `{domain_G : DomainG Σ}.
  Implicit Types l : loc.
  Implicit Types v t fn : val.
  Implicit Types Ψ : val → iProp Σ.

  Definition domain_spawn : val :=
    λ: "fn",
      let: "t" := ref NONE in
      Fork ("t" <- SOME ("fn" #())) ;;
      "t".

  Definition domain_join : val :=
    rec: "domain_join" "t" :=
      match: !"t" with
        NONE => "domain_join" "t"
      | SOME "v" => "v"
      end.

  Notation domain_meta_model :=
    (nroot .@ "model").

  Definition domain_model t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l domain_meta_model γ ∗
    excl γ ().

  #[local] Definition domain_inv_inner l γ Ψ : iProp Σ :=
    ∃ o,
    l ↦ o ∗
    (⌜o = NONEV⌝ ∨ ∃ v, ⌜o = SOMEV v⌝ ∗ (Ψ v ∨ excl γ ())).
  Definition domain_inv t ι Ψ : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l domain_meta_model γ ∗
    inv ι (domain_inv_inner l γ Ψ).

  #[global] Instance domain_inv_contractive t ι n :
    Proper (pointwise_relation val (dist_later n) ==> (≡{n}≡)) (domain_inv t ι).
  Proof.
    rewrite /domain_inv /domain_inv_inner. solve_contractive.
  Qed.
  #[global] Instance domain_inv_ne t ι n :
    Proper (pointwise_relation val (≡{n}≡) ==> (≡{n}≡)) (domain_inv t ι).
  Proof.
    intros Ψ1 Ψ2 HΨ. f_equiv. intros v. apply dist_dist_later. done.
  Qed.
  #[global] Instance domain_inv_proper t ι :
    Proper (pointwise_relation val (≡) ==> (≡)) (domain_inv t ι).
  Proof.
    intros Ψ1 Ψ2 HΨ. rewrite equiv_dist. intros n. f_equiv.
    intros v. revert n. rewrite -equiv_dist //.
  Qed.

  #[global] Instance domain_model_timeless t :
    Timeless (domain_model t).
  Proof.
    apply _.
  Qed.
  #[global] Instance domain_inv_persistent t ι Ψ :
    Persistent (domain_inv t ι Ψ).
  Proof.
    apply _.
  Qed.

  Lemma domain_spawn_spec ι fn Ψ :
    {{{ WP fn #() {{ Ψ }} }}}
      domain_spawn fn
    {{{ t, RET t; domain_inv t ι Ψ ∗ domain_model t }}}.
  Proof.
    iIntros "%Φ HΨ HΦ".
    wp_rec. wp_pures.
    wp_apply (wp_alloc with "[//]"). iIntros "%l (Hl & Hmeta)".
    wp_pures.
    iMod (excl_alloc (excl_G := domain_G_model_G) ()) as "(%γ & Hmodel)".
    iDestruct (meta_token_difference _ (↑domain_meta_model) with "Hmeta") as "(Hmeta_model & _)"; first solve_ndisj.
    iMod (meta_set _ _ γ domain_meta_model with "Hmeta_model") as "#Hmeta_model"; first done.
    iMod (inv_alloc ι _ (domain_inv_inner l γ Ψ) with "[Hl]") as "#Hinv".
    { iExists NONEV. auto with iFrame. }
    wp_apply (wp_fork with "[HΨ]").
    { iNext.
      wp_bind (fn #()). iApply (wp_wand with "HΨ"). iIntros "%v HΨ".
      wp_pures.
      iInv "Hinv" as "(%o & Hl & _)".
      wp_store.
      iModIntro. rewrite right_id. iExists (SOMEV v). auto 10 with iFrame.
    }
    wp_pures.
    iApply "HΦ". iSplitR; iExists l, γ; auto with iFrame.
  Qed.

  Lemma domain_join_spec t ι Ψ :
    {{{ domain_inv t ι Ψ ∗ domain_model t }}}
      domain_join t
    {{{ v, RET v; Ψ v }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta_model & #Hinv) & (%_l & %_γ & %Heq & #_Hmeta_model & Hmodel)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta_model _Hmeta_model") as %<-. iClear "_Hmeta_model".
    iLöb as "IH".
    wp_rec.
    wp_bind (!_)%E.
    iInv "Hinv" as "(%o & Hl & HΨ)".
    wp_load.
    iDestruct "HΨ" as "[-> | (%v & -> & [HΨ | Hmodel'])]"; iModIntro.
    - iSplitL "Hl".
      { iExists NONEV. auto with iFrame. }
      wp_pures.
      iApply ("IH" with "Hmodel HΦ").
    - iSplitL "Hl Hmodel".
      { iExists (SOMEV v). auto 10 with iFrame. }
      wp_pures.
      iApply ("HΦ" with "HΨ").
    - iDestruct (excl_exclusive with "Hmodel Hmodel'") as %[].
  Qed.
End domain_G.

#[global] Opaque domain_spawn.
#[global] Opaque domain_join.

#[global] Opaque domain_model.
#[global] Opaque domain_inv.