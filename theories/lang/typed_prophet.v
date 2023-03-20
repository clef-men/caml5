From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.

Record typed_prophet := {
  typed_prophet_type : Type ;
  typed_prophet_of_val : val → val → option typed_prophet_type ;
  typed_prophet_to_val : typed_prophet_type → val * val ;

  typed_prophet_of_to_val proph w v :
    (w, v) = typed_prophet_to_val proph →
    typed_prophet_of_val w v = Some proph ;
}.
#[global] Arguments Build_typed_prophet {_ _ _} _.

Section typed_prophet.
  Context `{!heapGS Σ} (prophet : typed_prophet).

  #[local] Fixpoint typed_prophet_process prophs :=
    match prophs with
    | [] =>
        []
    | (w, v) :: prophs =>
        match prophet.(typed_prophet_of_val) w v with
        | None =>
            []
        | Some proph =>
            proph :: typed_prophet_process prophs
        end
    end.
  Definition typed_prophet_model p prophs : iProp Σ :=
    ∃ pvs,
    ⌜prophs = typed_prophet_process pvs⌝ ∗ proph p pvs.

  #[global] Instance typed_prophet_model_timeless p prophs :
    Timeless (typed_prophet_model p prophs).
  Proof.
    apply _.
  Qed.

  Lemma typed_prophet_model_exclusive p prophs1 prophs2 :
    typed_prophet_model p prophs1 -∗
    typed_prophet_model p prophs2 -∗
    False.
  Proof.
    iIntros "* (%pvs1 & _ & Hp1) (%pvs2 & _ & Hp2)".
    iApply (proph_exclusive with "Hp1 Hp2").
  Qed.

  Lemma typed_prophet_new_proph_spec E :
    {{{ True }}}
      NewProph @ E
    {{{ p prophs, RET #p; typed_prophet_model p prophs }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (wp_new_proph with "[//]"). iIntros "%pvs %p Hp".
    iApply "HΦ". iExists pvs. auto with iFrame.
  Qed.

  Lemma typed_prophet_resolve_spec e v E p prophs Φ :
    Atomic StronglyAtomic e →
    to_val e = None →
    typed_prophet_model p prophs -∗
    WP e @ E {{ w,
      ∃ proph,
      ⌜(w, v) = prophet.(typed_prophet_to_val) proph⌝ ∗
        ∀ prophs',
        ⌜prophs = proph :: prophs'⌝ -∗
        typed_prophet_model p prophs' -∗
        Φ w
    }} -∗
    WP Resolve e #p v @ E {{ Φ }}.
  Proof.
    iIntros "% % (%pvs & %Hprophs & Hp) HΦ".
    wp_apply (wp_resolve with "Hp"); first done.
    wp_apply (wp_wand with "HΦ"). iIntros "%w (%proph & % & HΦ) %pvs' -> Hp".
    rewrite /= (typed_prophet_of_to_val _ proph) in Hprophs; last done.
    iApply "HΦ"; first done. iExists pvs'. auto with iFrame.
  Qed.
End typed_prophet.

#[global] Opaque typed_prophet_model.
