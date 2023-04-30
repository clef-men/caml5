From caml5 Require Import
  prelude.
From caml5.common Require Import
  tactics.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.concurrent Require Export
  base.

Implicit Types v w t : val.
Implicit Types vs : list val.

Record ws_deque `{!heapGS Σ} {unboxed : bool} := {
  ws_deque_make : val ;
  ws_deque_push : val ;
  ws_deque_pop : val ;
  ws_deque_steal : val ;

  ws_deque_name : Type ;
  ws_deque_name_eq_dec :
    EqDecision ws_deque_name ;
  ws_deque_name_countable :
    Countable ws_deque_name ;

  ws_deque_inv : val → ws_deque_name → namespace → iProp Σ ;
  ws_deque_model : val → ws_deque_name → list val → iProp Σ ;
  ws_deque_owner : val → ws_deque_name → iProp Σ ;

  ws_deque_inv_persistent t γ ι :
    Persistent (ws_deque_inv t γ ι) ;
  ws_deque_model_timeless t γ vs :
    Timeless (ws_deque_model t γ vs) ;
  ws_deque_owner_timeless t γ :
    Timeless (ws_deque_owner t γ) ;

  ws_deque_owner_exclusive t γ :
    ws_deque_owner t γ -∗
    ws_deque_owner t γ -∗
    False ;

  ws_deque_make_spec ι :
    {{{ True }}}
      ws_deque_make #()
    {{{ t γ, RET t; ws_deque_inv t γ ι ∗ ws_deque_model t γ [] ∗ ws_deque_owner t γ }}} ;

  ws_deque_push_spec t γ ι v :
    <<<
      ws_deque_inv t γ ι ∗ ws_deque_owner t γ |
      ∀∀ vs, ws_deque_model t γ vs
    >>>
      ws_deque_push t v @ ↑ι
    <<<
      ws_deque_model t γ (vs ++ [v]) |
      RET #(); ws_deque_owner t γ
    >>> ;

  ws_deque_pop_spec t γ ι :
    <<<
      ws_deque_inv t γ ι ∗ ws_deque_owner t γ |
      ∀∀ vs, ws_deque_model t γ vs
    >>>
      ws_deque_pop t @ ↑ι
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ ws_deque_model t γ []) ∨
      (∃ vs' v, ⌜vs = vs' ++ [v] ∧ o = SOMEV v⌝ ∗ ws_deque_model t γ vs') |
      RET o; ws_deque_owner t γ
    >>> ;

  ws_deque_steal_spec t γ ι :
    <<<
      ws_deque_inv t γ ι |
      ∀∀ vs, ws_deque_model t γ vs
    >>>
      ws_deque_steal t @ ↑ι
    <<< ∃∃ o,
      (⌜vs = [] ∧ o = NONEV⌝ ∗ ws_deque_model t γ []) ∨
      (∃ v vs', ⌜vs = v :: vs' ∧ o = SOMEV v⌝ ∗ ws_deque_model t γ vs') |
      RET o; True
    >>> ;

  ws_deque_unboxed :
    if unboxed then ∀ t γ ι,
      ws_deque_inv t γ ι -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments ws_deque _ {_} _ : assert.
#[global] Arguments Build_ws_deque {_ _} _ {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ : assert.
#[global] Existing Instance ws_deque_name_eq_dec.
#[global] Existing Instance ws_deque_name_countable.
#[global] Existing Instance ws_deque_inv_persistent.
#[global] Existing Instance ws_deque_model_timeless.
#[global] Existing Instance ws_deque_owner_timeless.

Program Definition ws_deque_wrap `{!heapGS Σ} `(base : ws_deque Σ unboxed) : ws_deque Σ unboxed := {|
  ws_deque_make :=
    base.(ws_deque_make) ;
  ws_deque_push :=
    λ: "t" "v",
      base.(ws_deque_push) "t" (ref "v") ;
  ws_deque_pop :=
    λ: "t",
      match: base.(ws_deque_pop) "t" with
        NONE => NONE
      | SOME "ref" => SOME (!"ref")
      end ;
  ws_deque_steal :=
    λ: "t",
      match: base.(ws_deque_steal) "t" with
        NONE => NONE
      | SOME "ref" => SOME (!"ref")
      end ;

  ws_deque_inv :=
    base.(ws_deque_inv) ;
  ws_deque_model t γ vs := (
    ∃ ls,
    base.(ws_deque_model) t γ (LitV ∘ LitLoc <$> ls) ∗
    [∗ list] l; v ∈ ls; vs, l ↦ v
  )%I ;
  ws_deque_owner :=
    base.(ws_deque_owner) ;
|}.
Next Obligation.
  intros. eauto using base.(ws_deque_owner_exclusive).
Qed.
Next Obligation.
  iIntros "* _ HΦ".
  wp_apply (base.(ws_deque_make_spec) with "[//]"). iIntros "%t %γ (#Hinv & Hmodel & Howner)".
  iApply "HΦ". iFrame "#∗". iExists []. naive_solver.
Qed.
Next Obligation.
  iIntros "* !> %Φ (#Hinv & Howner) HΦ".
  wp_pures. wp_alloc l as "Hl".
  awp_apply (base.(ws_deque_push_spec) with "[$Hinv $Howner]").
  iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs (%ls & Hmodel & Hls)".
  iAaccIntro with "Hmodel"; iIntros "Hmodel !>".
  - iFrame. iSplitL; auto with iFrame.
  - iRight. iSplitL; last naive_solver.
    iExists (ls ++ [l]). rewrite -fmap_snoc. iFrame. done.
Qed.
Next Obligation.
  iIntros "* !> %Φ (#Hinv & Howner) HΦ".
  wp_pures.
  awp_apply (base.(ws_deque_pop_spec) with "[$Hinv $Howner]").
  iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs (%ls & Hmodel & Hls)".
  iAaccIntro with "Hmodel".
  - iIntros "Hmodel !>". iFrame. iSplitL; auto with iFrame.
  - iIntros "% [((%Heq & ->) & Hmodel) | (%ws & %w & (%Heq & ->) & Hmodel)] !>"; iRight.
    + apply fmap_nil_inv in Heq as ->. iDestruct (big_sepL2_nil_inv_l with "Hls") as %->.
      iExists NONEV. iSplitL; first naive_solver. iIntros "HΦ !> Howner".
      wp_pures.
      iApply ("HΦ" with "Howner").
    + generalize dependent ls. refine (rev_ind _ _ _); [intros Heq | intros l ls _ Heq].
      { rewrite fmap_nil in Heq. edestruct app_cons_not_nil. done. }
      rewrite fmap_app app_inj_tail_iff in Heq. destruct Heq as (<- & <-).
      generalize dependent vs. apply rev_ind; [| intros v vs _].
      { iDestruct (big_sepL2_nil_inv_r with "Hls") as %?.
        edestruct app_cons_not_nil. done.
      }
      iDestruct (big_sepL2_snoc with "Hls") as "(Hls & Hl)".
      iExists (SOMEV v). iSplitR "Hl".
      * iRight. auto with iFrame.
      * iIntros "HΦ !> Howner".
        wp_pures. wp_load. wp_pures.
        iApply ("HΦ" with "Howner").
Qed.
Next Obligation.
  iIntros "* !> %Φ #Hinv HΦ".
  wp_pures.
  awp_apply (base.(ws_deque_steal_spec) with "Hinv").
  iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs (%ls & Hmodel & Hls)".
  iAaccIntro with "Hmodel".
  - iIntros "Hmodel !>". iFrame. iSplitL; auto with iFrame.
  - iIntros "% [((%Heq & ->) & Hmodel) | (%w & %ws & (%Heq & ->) & Hmodel)] !>"; iRight.
    + apply fmap_nil_inv in Heq as ->. iDestruct (big_sepL2_nil_inv_l with "Hls") as %->.
      iExists NONEV. iSplitL; first naive_solver. iIntros "HΦ !> _".
      wp_pures.
      iApply ("HΦ" with "[//]").
    + destruct ls as [| l ls]; simplify.
      destruct vs as [| v vs].
      { iDestruct (big_sepL2_nil_inv_r with "Hls") as %?. simplify. }
      iDestruct (big_sepL2_cons with "Hls") as "(Hl & Hls)".
      iExists (SOMEV v). iSplitR "Hl".
      * iRight. auto with iFrame.
      * iIntros "HΦ !> Howner".
        wp_pures. wp_load. wp_pures.
        iApply ("HΦ" with "Howner").
Qed.
Next Obligation.
  intros. destruct unboxed; eauto using base.(ws_deque_unboxed).
Qed.
