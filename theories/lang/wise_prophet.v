From caml5 Require Import
  prelude.
From caml5.base_logic Require Import
  lib.agree
  lib.mono_list.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.lang Require Export
  typed_prophet.

Class WiseProphetG Σ `{!heapGS Σ} prophet := {
  wise_prophet_G_full_G : AgreeG Σ $ leibnizO (list prophet.(typed_prophet_type)) ;
  wise_prophet_G_past_G : mono_listG prophet.(typed_prophet_type) Σ ;
}.
#[local] Existing Instance wise_prophet_G_full_G.
#[local] Existing Instance wise_prophet_G_past_G.

Definition wise_prophet_Σ prophet := #[
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
  Context `{!heapGS Σ} prophet `{!WiseProphetG Σ prophet}.

  Definition wise_prophet_name : Type := gname * gname.

  #[global] Instance wise_prophet_name_eq_dec :
    EqDecision wise_prophet_name.
  Proof.
    apply _.
  Defined.
  #[global] Instance wise_prophet_name_countable :
    Countable wise_prophet_name.
  Proof.
    apply _.
  Qed.

  Notation prophecies := (list prophet.(typed_prophet_type)).
  Let prophecies_O := leibnizO prophecies.
  #[local] Canonical prophecies_O.

  Implicit Types γ : wise_prophet_name.
  Implicit Types prophs : prophecies.

  Notation "γ '.(full)'" := γ.1
  ( at level 5
  ) : stdpp_scope.
  Notation "γ '.(past)'" := γ.2
  ( at level 5
  ) : stdpp_scope.

  Definition wise_prophet_model p γ past prophs : iProp Σ :=
    agree_on γ.(full) (past ++ prophs) ∗
    mono_list_auth γ.(past) 1 past ∗
    typed_prophet_model prophet p prophs.

  Definition wise_prophet_lb γ lb : iProp Σ :=
    ∃ past_lb,
    agree_on γ.(full) (past_lb ++ lb) ∗
    mono_list_lb γ.(past) past_lb.

  #[global] Instance wise_prophet_model_timeless p γ past prophs :
    Timeless (wise_prophet_model p γ past prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_prophet_lb_timeless γ lb :
    Timeless (wise_prophet_lb γ lb).
  Proof.
    apply _.
  Qed.
  #[global] Instance wise_prophet_lb_persistent γ lb :
    Persistent (wise_prophet_lb γ lb).
  Proof.
    apply _.
  Qed.

  Lemma wise_prophet_model_exclusive p γ1 past1 prophs1 γ2 past2 prophs2 :
    wise_prophet_model p γ1 past1 prophs1 -∗
    wise_prophet_model p γ2 past2 prophs2 -∗
    False.
  Proof.
    iIntros "(_ & _ & Hmodel1) (_ & _ & Hmodel2)".
    iApply (typed_prophet_model_exclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma wise_prophet_lb_get p γ past prophs :
    wise_prophet_model p γ past prophs -∗
    wise_prophet_lb γ prophs.
  Proof.
    iIntros "(#Hfull & Hpast_auth & Hmodel)".
    iExists past. iFrame "#∗". iApply (mono_list_lb_get with "Hpast_auth").
  Qed.
  Lemma wise_prophet_model_lb_valid p γ past prophs lb :
    wise_prophet_model p γ past prophs -∗
    wise_prophet_lb γ lb -∗
    ⌜∃ past1 past2, past = past1 ++ past2 ∧ lb = past2 ++ prophs⌝.
  Proof.
    iIntros "(#Hfull & Hpast_auth & Hmodel) (%past1 & #Hfull' & #Hpast_lb)".
    iDestruct (agree_on_agree_L with "Hfull Hfull'") as %Hfull.
    iDestruct (mono_list_auth_lb_valid with "Hpast_auth Hpast_lb") as %(_ & past2 & ->).
    iExists past1, past2. rewrite -assoc in Hfull. naive_solver.
  Qed.

  Lemma wise_prophet_new_proph_spec E :
    {{{ True }}}
      NewProph @ E
    {{{ p γ prophs,
      RET #p;
      wise_prophet_model p γ [] prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_fupd. wp_apply (typed_prophet_new_proph_spec with "[//]"). iIntros "%p %prophs Hp".
    iMod (agree_alloc prophs) as "(%γ_full & #Hfull)".
    iMod (mono_list_alloc []) as "(%γ_past & Hpast_auth & _)".
    iApply ("HΦ" $! _ (γ_full, γ_past)). iFrame "#∗". done.
  Qed.

  Lemma wise_prophet_resolve_spec e v E p γ past prophs Φ :
    Atomic StronglyAtomic e →
    to_val e = None →
    wise_prophet_model p γ past prophs -∗
    WP e @ E {{ w,
      ∃ proph,
      ⌜(w, v) = prophet.(typed_prophet_to_val) proph⌝ ∗
        ∀ prophs',
        ⌜prophs = proph :: prophs'⌝ -∗
        wise_prophet_model p γ (past ++ [proph]) prophs' -∗
        Φ w
    }} -∗
    WP Resolve e #p v @ E {{ Φ }}.
  Proof.
    iIntros "% % (#Hfull & Hpast_auth & Hmodel) HΦ".
    wp_apply (typed_prophet_resolve_spec with "Hmodel"); first done.
    iApply wp_fupd. wp_apply (wp_wand with "HΦ"). iIntros "%w HΦ".
    iDestruct "HΦ" as "(%proph & % & HΦ)".
    iExists proph. iSplitR; first done.
    iMod (mono_list_auth_update_app [proph] with "Hpast_auth") as "(Hpast_auth & _)".
    iIntros "!> %prophs' -> Hp".
    iApply ("HΦ" with "[//]"). iFrame. list_simplifier. done.
  Qed.
End wise_prophet.

#[global] Opaque wise_prophet_name.
#[global] Opaque wise_prophet_model.
#[global] Opaque wise_prophet_lb.
