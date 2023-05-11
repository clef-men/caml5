From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.concurrent Require Export
  counter.

Implicit Types v t : val.
Implicit Types vs : list val.
Implicit Types vss : list (list val).

Record ws_deques_ext1 `{!heapGS Σ} `{!CounterG Σ} {unboxed : bool} := {
  ws_deques_ext1_make : val ;
  ws_deques_ext1_push : val ;
  ws_deques_ext1_pop : val ;
  ws_deques_ext1_try_steal_once : val ;

  ws_deques_ext1_name : Type ;
  ws_deques_ext1_name_eq_dec :
    EqDecision ws_deques_ext1_name ;
  ws_deques_ext1_name_countable :
    Countable ws_deques_ext1_name ;

  ws_deques_ext1_inv : val → ws_deques_ext1_name → namespace → val → nat → iProp Σ ;
  ws_deques_ext1_model : val → ws_deques_ext1_name → list (list val) → iProp Σ ;

  ws_deques_ext1_inv_persistent t γ ι cntr sz :
    Persistent (ws_deques_ext1_inv t γ ι cntr sz) ;
  ws_deques_ext1_model_timeless t γ vss :
    Timeless (ws_deques_ext1_model t γ vss) ;

  ws_deques_ext1_make_spec ι cntr ι_cntr sz sz' :
    sz' = Z.of_nat sz →
    {{{ counter_inv cntr ι_cntr (Some sz) }}}
      ws_deques_ext1_make #sz'
    {{{ t γ,
      RET t;
      ws_deques_ext1_inv t γ ι cntr sz ∗
      ws_deques_ext1_model t γ (repeat [] sz)
    }}} ;

  ws_deques_ext1_push_spec t γ ι cntr sz i i' v :
    i' = Z.of_nat i →
    <<<
      ws_deques_ext1_inv t γ ι cntr sz ∗
      counter_token cntr i
    | ∀∀ vss, ws_deques_ext1_model t γ vss
    >>>
      ws_deques_ext1_push t #i' v @ ↑ι
    <<< ∃∃ vs,
      ⌜vss !! i = Some vs⌝ ∗
      ws_deques_ext1_model t γ (<[i := vs ++ [v]]> vss)
    | RET #(); counter_token cntr i
    >>> ;

  ws_deques_ext1_pop_spec t γ ι cntr sz i i' :
    i' = Z.of_nat i →
    <<<
      ws_deques_ext1_inv t γ ι cntr sz ∗
      counter_token cntr i
    | ∀∀ vss, ws_deques_ext1_model t γ vss
    >>>
      ws_deques_ext1_pop t #i' @ ↑ι
    <<< ∃∃ o,
        ⌜vss !! i = Some [] ∧ o = NONEV⌝ ∗
        ws_deques_ext1_model t γ vss
      ∨ ∃ vs v,
        ⌜vss !! i = Some (vs ++ [v]) ∧ o = SOMEV v⌝ ∗
        ws_deques_ext1_model t γ (<[i := vs]> vss)
    | RET o; counter_token cntr i
    >>> ;

  ws_deques_ext1_try_steal_once_spec t γ ι cntr sz i i' :
    i' = Z.of_nat i →
    <<<
      ws_deques_ext1_inv t γ ι cntr sz ∗
      counter_token cntr i
    | ∀∀ vss, ws_deques_ext1_model t γ vss
    >>>
      ws_deques_ext1_try_steal_once t #i' @ ↑ι
    <<< ∃∃ o,
        ⌜o = NONEV⌝ ∗
        ws_deques_ext1_model t γ vss
      ∨ ∃ j v vs,
        ⌜j ≠ i ∧ vss !! j = Some (v :: vs) ∧ o = SOMEV v⌝ ∗
        ws_deques_ext1_model t γ (<[j := vs]> vss)
    | RET o; counter_token cntr i
    >>> ;

  ws_deques_ext1_unboxed :
    if unboxed then ∀ t γ ι cntr sz,
      ws_deques_ext1_inv t γ ι cntr sz -∗
      ⌜val_is_unboxed t⌝
    else
      True ;
}.
#[global] Arguments ws_deques_ext1 _ {_ _} _ : assert.
#[global] Arguments Build_ws_deques_ext1 {_ _ _} _ {_ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ : assert.
#[global] Existing Instance ws_deques_ext1_name_eq_dec.
#[global] Existing Instance ws_deques_ext1_name_countable.
#[global] Existing Instance ws_deques_ext1_inv_persistent.
#[global] Existing Instance ws_deques_ext1_model_timeless.

Section ws_deques_ext1.
  Context `{!heapGS Σ} `{!CounterG Σ} `(ws_deques : ws_deques_ext1 Σ unboxed).

  Definition ws_deques_ext1_try_steal : val :=
    rec: "ws_deques_ext1_try_steal" "t" "i" "cnt" :=
      if: "cnt" ≤ #0 then (
        NONE
      ) else (
        match: ws_deques.(ws_deques_ext1_try_steal_once) "t" "i" with
          NONE => "ws_deques_ext1_try_steal" "t" "i" ("cnt" - #1)
        | SOME "v" => SOME "v"
        end
      ).
  Definition ws_deques_ext1_steal : val :=
    rec: "ws_deques_ext1_steal" "t" "i" :=
      match: ws_deques.(ws_deques_ext1_try_steal_once) "t" "i" with
        NONE => "ws_deques_ext1_steal" "t" "i"
      | SOME "v" => SOME "v"
      end.

  Definition ws_deques_ext1_pop_try_steal : val :=
    λ: "t" "i" "cnt",
      match: ws_deques.(ws_deques_ext1_pop) "t" "i" with
        NONE => ws_deques_ext1_try_steal "t" "i" "cnt"
      | SOME "v" => SOME "v"
      end.
  Definition ws_deques_ext1_pop_steal : val :=
    λ: "t" "i",
      match: ws_deques.(ws_deques_ext1_pop) "t" "i" with
        NONE => ws_deques_ext1_steal "t" "i"
      | SOME "v" => SOME "v"
      end.

  Lemma ws_deques_ext1_try_steal_spec t γ ι cntr sz i i' (cnt : Z) :
    i' = Z.of_nat i →
    <<<
      ws_deques.(ws_deques_ext1_inv) t γ ι cntr sz ∗
      counter_token cntr i
    | ∀∀ vss, ws_deques.(ws_deques_ext1_model) t γ vss
    >>>
      ws_deques_ext1_try_steal t #i' #cnt @ ↑ι
    <<< ∃∃ o,
        ⌜o = NONEV⌝ ∗
        ws_deques.(ws_deques_ext1_model) t γ vss
      ∨ ∃ j v vs,
        ⌜j ≠ i ∧ vss !! j = Some (v :: vs) ∧ o = SOMEV v⌝ ∗
        ws_deques.(ws_deques_ext1_model) t γ (<[j := vs]> vss)
    | RET o; counter_token cntr i
    >>>.
  Proof.
    iIntros (->) "!> %Φ (#Hinv & Hcounter_token) HΦ".
    iLöb as "IH" forall (cnt).
    wp_rec. wp_pures.
    case_decide as Hcnt; wp_pures.
    - iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
      iMod ("HΦ" $! NONEV with "[Hmodel]") as "HΦ"; first auto.
      iApply ("HΦ" with "Hcounter_token").
    - wp_apply (ws_deques_ext1_try_steal_once_spec with "[$Hinv $Hcounter_token]"); first done.
      iAuIntro.
      iApply (aacc_aupd with "HΦ"); first done. iIntros "%vss Hmodel".
      iAaccIntro with "Hmodel"; first auto with iFrame. iIntros "%o [(-> & Hmodel) | (%j & %v & %vs & (%Hj & %Hlookup & ->) & Hmodel)] !>".
      + iLeft. iFrame. iIntros "HΦ !> Hcounter_token".
        wp_smart_apply ("IH" with "Hcounter_token HΦ").
      + iRight. iExists (SOMEV v). iSplitL.
        { iRight. iExists j, v, vs. auto. }
        iIntros "HΦ !> Hcounter_token".
        wp_pures.
        iApply ("HΦ" with "Hcounter_token").
  Qed.

  Lemma ws_deques_ext1_steal_spec t γ ι cntr sz i i' :
    i' = Z.of_nat i →
    <<<
      ws_deques.(ws_deques_ext1_inv) t γ ι cntr sz ∗
      counter_token cntr i
    | ∀∀ vss, ws_deques.(ws_deques_ext1_model) t γ vss
    >>>
      ws_deques_ext1_steal t #i' @ ↑ι
    <<< ∃∃ j v vs,
      ⌜j ≠ i ∧ vss !! j = Some (v :: vs)⌝ ∗
      ws_deques.(ws_deques_ext1_model) t γ (<[j := vs]> vss)
    | RET SOMEV v; counter_token cntr i
    >>>.
  Proof.
    iIntros (->) "!> %Φ (#Hinv & Hcounter_token) HΦ".
    iLöb as "IH".
    wp_rec. wp_pures.
    wp_apply (ws_deques_ext1_try_steal_once_spec with "[$Hinv $Hcounter_token]"); first done.
    iAuIntro.
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vss Hmodel".
    iAaccIntro with "Hmodel"; first auto with iFrame. iIntros "%o [(-> & Hmodel) | (%j & %v & %vs & (%Hj & %Hlookup & ->) & Hmodel)] !>".
    - iLeft. iFrame. iIntros "HΦ !> Hcounter_token".
      wp_smart_apply ("IH" with "Hcounter_token HΦ").
    - iRight. iExists j, v, vs. iSplitL; first auto. iIntros "HΦ !> Hcounter_token".
      wp_pures.
      iApply ("HΦ" with "Hcounter_token").
  Qed.

  Lemma ws_deques_ext1_pop_try_steal_spec t γ ι cntr sz i i' (cnt : Z) :
    i' = Z.of_nat i →
    <<<
      ws_deques.(ws_deques_ext1_inv) t γ ι cntr sz ∗
      counter_token cntr i
    | ∀∀ vss, ws_deques.(ws_deques_ext1_model) t γ vss
    >>>
      ws_deques_ext1_pop_try_steal t #i' #cnt @ ↑ι
    <<< ∃∃ o,
        ⌜o = NONEV⌝ ∗
        ws_deques.(ws_deques_ext1_model) t γ vss
      ∨ ∃ j vs v,
        ⌜(j = i ∧ vss !! i = Some (vs ++ [v]) ∨ j ≠ i ∧ vss !! j = Some (v :: vs)) ∧ o = SOMEV v⌝ ∗
        ws_deques.(ws_deques_ext1_model) t γ (<[j := vs]> vss)
    | RET o; counter_token cntr i
    >>>.
  Proof.
    iIntros (->) "!> %Φ (#Hinv & Hcounter_token) HΦ".
    wp_rec.
    wp_smart_apply (ws_deques_ext1_pop_spec with "[$Hinv $Hcounter_token]"); first done.
    iAuIntro.
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vss Hmodel".
    iAaccIntro with "Hmodel"; first auto with iFrame. iIntros "%o [((_ & ->) & Hmodel) | (%vs & %v & (%Hlookup & ->) & Hmodel)] !>".
    - iLeft. iFrame. iIntros "HΦ !> Hcounter_token".
      wp_smart_apply (ws_deques_ext1_try_steal_spec with "[$Hinv $Hcounter_token]"); first done.
      iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. clear. iIntros "%vss Hmodel".
      iAaccIntro with "Hmodel"; first auto with iFrame. iIntros "%o [(-> & Hmodel) | (%j & %v & %vs & (%Hj & %Hlookup & ->) & Hmodel)] !>".
      + iExists NONEV. iSplitL; first auto. iIntros "HΦ !> Hcounter_token".
        iApply ("HΦ" with "Hcounter_token").
      + iExists (SOMEV v). iSplitL.
        { iRight. iExists j, vs, v. auto 10 with iFrame. }
        iIntros "HΦ !> Hcounter_token".
        iApply ("HΦ" with "Hcounter_token").
    - iRight. iExists (SOMEV v). iSplitL.
      { iRight. iExists i, vs, v. auto 10 with iFrame. }
      iIntros "HΦ !> Hcounter_token".
      wp_pures.
      iApply ("HΦ" with "Hcounter_token").
  Qed.

  Lemma ws_deques_ext1_pop_steal_spec t γ ι cntr sz i i' :
    i' = Z.of_nat i →
    <<<
      ws_deques.(ws_deques_ext1_inv) t γ ι cntr sz ∗
      counter_token cntr i
    | ∀∀ vss, ws_deques.(ws_deques_ext1_model) t γ vss
    >>>
      ws_deques_ext1_pop_steal t #i' @ ↑ι
    <<< ∃∃ j vs v,
      ⌜j = i ∧ vss !! i = Some (vs ++ [v]) ∨ j ≠ i ∧ vss !! j = Some (v :: vs)⌝ ∗
      ws_deques.(ws_deques_ext1_model) t γ (<[j := vs]> vss)
    | RET SOMEV v; counter_token cntr i
    >>>.
  Proof.
    iIntros (->) "!> %Φ (#Hinv & Hcounter_token) HΦ".
    wp_rec.
    wp_smart_apply (ws_deques_ext1_pop_spec with "[$Hinv $Hcounter_token]"); first done.
    iAuIntro.
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vss Hmodel".
    iAaccIntro with "Hmodel"; first auto with iFrame. iIntros "%o [((_ & ->) & Hmodel) | (%vs & %v & (%Hlookup & ->) & Hmodel)] !>".
    - iLeft. iFrame. iIntros "HΦ !> Hcounter_token".
      wp_smart_apply (ws_deques_ext1_steal_spec with "[$Hinv $Hcounter_token]"); first done.
      iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. clear. iIntros "%vss Hmodel".
      iAaccIntro with "Hmodel"; first auto with iFrame. iIntros "%j %v %vs ((%Hj & %Hlookup) & Hmodel) !>".
      iExists j, vs, v. iSplitL; first auto. iIntros "HΦ !> Hcounter_token".
      iApply ("HΦ" with "Hcounter_token").
    - iRight. iExists i, vs, v. iSplitL; first auto. iIntros "HΦ !> Hcounter_token".
      wp_pures.
      iApply ("HΦ" with "Hcounter_token").
  Qed.
End ws_deques_ext1.

#[global] Opaque ws_deques_ext1_try_steal.
#[global] Opaque ws_deques_ext1_steal.
#[global] Opaque ws_deques_ext1_pop_try_steal.
#[global] Opaque ws_deques_ext1_pop_steal.

Notation "ws_deques .(ws_deques_ext1_try_steal)" := (ws_deques_ext1_try_steal ws_deques)
( at level 5
).
Notation "ws_deques .(ws_deques_ext1_steal)" := (ws_deques_ext1_steal ws_deques)
( at level 5
).
Notation "ws_deques .(ws_deques_ext1_pop_try_steal)" := (ws_deques_ext1_pop_try_steal ws_deques)
( at level 5
).
Notation "ws_deques .(ws_deques_ext1_pop_steal)" := (ws_deques_ext1_pop_steal ws_deques)
( at level 5
).