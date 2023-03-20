From caml5 Require Import
  prelude.
From caml5.base_logic Require Import
  lib.auth_excl
  lib.agree
  lib.mono_list.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.lang Require Export
  typed_prophet.

Class WiseProphetG Σ `{!heapGS Σ} prophet := {
  wise_prophet_G_model_G : AuthExclG Σ $ leibnizO (list prophet.(typed_prophet_type)) ;
  wise_prophet_G_full_G : AgreeG Σ $ leibnizO (list prophet.(typed_prophet_type)) ;
  wise_prophet_G_past_G : mono_listG prophet.(typed_prophet_type) Σ ;
}.
#[local] Existing Instance wise_prophet_G_model_G.
#[local] Existing Instance wise_prophet_G_full_G.
#[local] Existing Instance wise_prophet_G_past_G.

Definition wise_prophet_Σ prophet := #[
  auth_excl_Σ $ leibnizO (list prophet.(typed_prophet_type)) ;
  agree_Σ $ leibnizO (list prophet.(typed_prophet_type)) ;
  mono_listΣ prophet.(typed_prophet_type)
].
Lemma subG_wise_prophet_Σ Σ `{!heapGS Σ} prophet :
  subG (wise_prophet_Σ prophet) Σ →
  WiseProphetG Σ prophet.
Proof.
  solve_inG.
Qed.

Section wise_prophet.
  Context `{!heapGS Σ} (prophet : typed_prophet) `{!WiseProphetG Σ prophet}.

  Definition wise_prophet_name := gname.

  Notation prophecies := (list prophet.(typed_prophet_type)).
  Let prophecies_O := leibnizO prophecies.
  #[local] Canonical prophecies_O.

  Implicit Types γ_model : wise_prophet_name.
  Implicit Types γ_full γ_past : gname.
  Implicit Types prophs : prophecies.

  Definition wise_prophet_model γ_model prophs :=
    auth_excl_auth γ_model (DfracOwn 1) prophs.

  #[local] Definition wise_prophet_inv_inner p γ_model γ_full γ_past : iProp Σ :=
    ∃ past prophs,
    typed_prophet_model prophet p prophs ∗
    auth_excl_frag γ_model prophs ∗
    agree_on γ_full (past ++ prophs) ∗
    mono_list_auth_own γ_past 1 past.
  Definition wise_prophet_inv p γ_model γ_full γ_past ι :=
    inv ι (wise_prophet_inv_inner p γ_model γ_full γ_past).

  #[global] Instance wise_prophet_model_timeless γ_model prophs :
    Timeless (wise_prophet_model γ_model prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_prophet_inv_persistent p γ_model γ_full γ_past ι :
    Persistent (wise_prophet_inv p γ_model γ_full γ_past ι).
  Proof.
    apply _.
  Qed.

  Lemma wise_prophet_model_exclusive p prophs1 prophs2 :
    wise_prophet_model p prophs1 -∗
    wise_prophet_model p prophs2 -∗
    False.
  Proof.
    apply auth_excl_auth_exclusive.
  Qed.

  Lemma wise_prophet_new_proph_spec ι E :
    {{{ True }}}
      NewProph @ E
    {{{ p γ_model γ_full γ_past prophs,
      RET #p;
      wise_prophet_inv p γ_model γ_full γ_past ι ∗
      wise_prophet_model γ_model prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_fupd. wp_apply (typed_prophet_new_proph_spec with "[//]"). iIntros "%p %prophs Hp".
    iMod (auth_excl_alloc' prophs) as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod (agree_alloc prophs) as "(%γ_full & #Hfull)".
    iMod (mono_list_own_alloc []) as "(%γ_past & Hpast & _)".
    iApply "HΦ". iFrame. iApply inv_alloc. iNext. iExists [], prophs. auto with iFrame.
  Qed.

  Lemma wise_prophet_resolve_spec e v E p γ_model γ_full γ_past ι prophs Φ :
    ↑ι ⊆ E →
    Atomic StronglyAtomic e →
    to_val e = None →
    wise_prophet_inv p γ_model γ_full γ_past ι -∗
    wise_prophet_model γ_model prophs -∗
    WP e @ E ∖ ↑ι {{ w,
      ∀ past,
      agree_on γ_full (past ++ prophs) -∗
      mono_list_auth_own γ_past 1 past ={E ∖ ↑ι}=∗
        ∃ proph,
        ⌜(w, v) = prophet.(typed_prophet_to_val) proph⌝ ∗
        mono_list_auth_own γ_past 1 past ∗
          ∀ prophs',
          ⌜prophs = proph :: prophs'⌝ -∗
          wise_prophet_model γ_model prophs' ={E ∖ ↑ι}=∗
          Φ w
    }} -∗
    WP Resolve e #p v @ E {{ Φ }}.
  Proof.
    iIntros "% % % Hinv Hmodel₁ HΦ".
    iInv "Hinv" as "(%past & %_prophs & >Hp & >Hmodel₂ & >#Hfull & >Hpast)"; first apply strongly_atomic_atomic, _.
    iDestruct (auth_excl_agree_L with "Hmodel₁ Hmodel₂") as %<-.
    wp_apply (typed_prophet_resolve_spec with "Hp"); first done.
    iApply wp_fupd. wp_apply (wp_wand with "HΦ"). iIntros "%w HΦ".
    iMod ("HΦ" with "Hfull Hpast") as "(%proph & % & Hpast & HΦ)".
    iModIntro. iExists proph. iSplitR; first done. iIntros "%prophs' -> Hp".
    iMod (auth_excl_update' prophs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod (mono_list_auth_own_update_app [proph] with "Hpast") as "(Hpast & _)".
    iMod ("HΦ" with "[//] Hmodel₁") as "$".
    iModIntro. iNext. iExists (past ++ [proph]), prophs'. iFrame. list_simplifier. done.
  Qed.
End wise_prophet.

#[global] Opaque wise_prophet_name.
#[global] Opaque wise_prophet_model.
#[global] Opaque wise_prophet_inv.
