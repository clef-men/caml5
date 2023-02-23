From caml5 Require Import
  prelude.
From caml5.lang Require Import
  notations
  proofmode.
From caml5.std Require Export
  chain.

Section heapGS.
  Context `{!heapGS Σ}.
  Implicit Types v w : val.

  Definition mlst_nil : val :=
    #().
  Definition mlst_cons :=
    chain_cons.
  Definition mlst_singleton : val :=
    λ: "v",
      mlst_cons "v" mlst_nil.

  Definition mlst_head :=
    chain_head.
  Definition mlst_tail :=
    chain_tail.

  Definition mlst_set_head :=
    chain_set_head.
  Definition mlst_set_tail :=
    chain_set_tail.

  Definition mlst_is_empty : val :=
    λ: "t",
      "t" = #().

  Definition mlst_advance :=
    chain_advance.

  Definition mlst_get :=
    chain_get.
  Definition mlst_set :=
    chain_set.

  Definition mlst_foldl : val :=
    rec: "mlst_foldl" "t" "acc" "fn" :=
      if: mlst_is_empty "t" then (
        "acc"
      ) else (
        "mlst_foldl" (mlst_tail "t") ("fn" "acc" (mlst_head "t")) "fn"
      ).
  Definition mlst_foldr : val :=
    rec: "mlst_foldr" "t" "fn" "acc" :=
      if: mlst_is_empty "t" then (
        "acc"
      ) else (
        "fn" (mlst_head "t") ("mlst_foldr" (mlst_tail "t") "fn" "acc")
      ).

  Definition mlst_size : val :=
    λ: "t",
      mlst_foldl "t" #0 (λ: "acc" <>, "acc" + #1).

  Definition mlst_rev : val :=
    λ: "t",
      mlst_foldl "t" mlst_nil (λ: "acc" "v", mlst_cons "v" "acc").

  Definition mlst_copy : val :=
    λ: "t",
      mlst_foldr "t" mlst_cons mlst_nil.

  Definition mlst_app : val :=
    λ: "t1" "t2",
      mlst_foldr "t1" mlst_cons "t2".
  Definition mlst_snoc : val :=
    λ: "t" "v",
      mlst_app "t" (mlst_singleton "v").

  Definition mlst_iter : val :=
    λ: "t" "fn",
      mlst_foldl "t" #() (λ: <> "v", "fn" "v").

  Definition mlst_map : val :=
    rec: "lst_map" "t" "fn" :=
      if: mlst_is_empty "t" then (
        mlst_nil
      ) else (
        let: "v" := "fn" "v" in
        let: "t" := "mlst" "t" "fn" in
        mlst_cons "v" "t"
      ).

  Definition mlst_model t dq vs :=
    chain_model t dq vs #().

  Lemma mlst_model_unboxed t dq vs :
    mlst_model t dq vs -∗
    ⌜val_is_unboxed t⌝.
  Proof.
    iIntros "Hmodel". destruct vs as [| v vs].
    - iDestruct (chain_model_nil_2 _ dq with "Hmodel") as %->. done.
    - iApply (chain_model_unboxed with "Hmodel").
  Qed.

  #[global] Instance mlst_model_timeless t dq vs :
    Timeless (mlst_model t dq vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mlst_model_persistent t vs :
    Persistent (mlst_model t DfracDiscarded vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance mlst_model_fractional t vs :
    Fractional (λ q, mlst_model t (DfracOwn q) vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mlst_model_as_fractional t q vs :
    AsFractional (mlst_model t (DfracOwn q) vs) (λ q, mlst_model t (DfracOwn q) vs) q.
  Proof.
    apply _.
  Qed.

  Lemma mlst_model_app dq t1 vs1 t2 vs2 :
    chain_model t1 dq vs1 t2 -∗
    mlst_model t2 dq vs2 -∗
    mlst_model t1 dq (vs1 ++ vs2) .
  Proof.
    apply chain_model_app_1.
  Qed.
  Lemma mlst_model_split vs1 vs2 t vs dq :
    vs = vs1 ++ vs2 →
    mlst_model t dq vs -∗
      ∃ t',
      chain_model t dq vs1 t' ∗
      mlst_model t' dq vs2.
  Proof.
    apply chain_model_app_2.
  Qed.

  Lemma mlst_model_persist t dq vs :
    mlst_model t dq vs ==∗
    mlst_model t DfracDiscarded vs.
  Proof.
    apply chain_model_persist.
  Qed.

  Lemma mlst_model_valid t dq vs :
    0 < length vs →
    mlst_model t dq vs -∗
    ⌜✓ dq⌝.
  Proof.
    apply chain_model_valid.
  Qed.
  Lemma mlst_model_combine t dq1 vs1 dq2 vs2 :
    mlst_model t dq1 vs1 -∗
    mlst_model t dq2 vs2 -∗
      mlst_model t (dq1 ⋅ dq2) vs1 ∗
      ⌜vs1 = vs2⌝.
  Proof.
    iIntros "Hmodel1 Hmodel2".
    destruct (Nat.lt_total (length vs1) (length vs2)) as [| []].
    - iDestruct (chain_model_combine with "Hmodel1 Hmodel2") as "(_ & Hmodel2 & _)"; first lia.
      assert (0 < length (drop (length vs1) vs2)) by (rewrite drop_length; lia).
      destruct (drop (length vs1) vs2); list_simplifier; first lia.
      iDestruct "Hmodel2" as "(%l2 & %_ & % & _)". done.
    - iDestruct (chain_model_combine' with "Hmodel1 Hmodel2") as "($ & $ & _)"; first lia.
    - iDestruct (chain_model_combine with "Hmodel2 Hmodel1") as "(_ & Hmodel1 & _)"; first lia.
      assert (0 < length (drop (length vs2) vs1)) by (rewrite drop_length; lia).
      destruct (drop (length vs2) vs1); list_simplifier; first lia.
      iDestruct "Hmodel1" as "(%l1 & %_ & % & _)". done.
  Qed.
  Lemma mlst_model_valid_2 t dq1 vs1 dq2 vs2 :
    0 < length vs1 →
    mlst_model t dq1 vs1 -∗
    mlst_model t dq2 vs2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ vs1 = vs2⌝.
  Proof.
    iIntros "% Hmodel1 Hmodel2".
    iDestruct (mlst_model_combine with "Hmodel1 Hmodel2") as "(Hmodel & ->)".
    iDestruct (mlst_model_valid with "Hmodel") as %?; done.
  Qed.
  Lemma mlst_model_agree t dq1 vs1 dq2 vs2 :
    mlst_model t dq1 vs1 -∗
    mlst_model t dq2 vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    iIntros "Hmodel1 Hmodel2".
    iDestruct (mlst_model_combine with "Hmodel1 Hmodel2") as "(_ & <-)"; done.
  Qed.
  Lemma mlst_model_dfrac_ne t1 dq1 vs1 t2 dq2 vs2 :
    0 < length vs1 →
    ¬ ✓ (dq1 ⋅ dq2) →
    mlst_model t1 dq1 vs1 -∗
    mlst_model t2 dq2 vs2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    iIntros "% % Hmodel1 Hmodel2" (->).
    iDestruct (mlst_model_valid_2 with "Hmodel1 Hmodel2") as %?; naive_solver.
  Qed.
  Lemma mlst_model_ne t1 vs1 t2 dq2 vs2 :
    0 < length vs1 →
    mlst_model t1 (DfracOwn 1) vs1 -∗
    mlst_model t2 dq2 vs2 -∗
    ⌜t1 ≠ t2⌝.
  Proof.
    intros. iApply mlst_model_dfrac_ne; [done | intros []%exclusive_l; apply _].
  Qed.
  Lemma mlst_model_exclusive t vs1 vs2 :
    0 < length vs1 →
    mlst_model t (DfracOwn 1) vs1 -∗
    mlst_model t (DfracOwn 1) vs2 -∗
    False.
  Proof.
    iIntros "% Hmodel1 Hmodel2".
    iDestruct (mlst_model_ne with "Hmodel1 Hmodel2") as %?; naive_solver.
  Qed.

  Lemma mlst_nil_spec :
    ⊢ mlst_model mlst_nil (DfracOwn 1) [].
  Proof.
    iApply chain_model_nil_1.
  Qed.
  Lemma mlst_cons_spec t dq vs v :
    ✓ dq →
    {{{ mlst_model t dq vs }}}
      mlst_cons v t
    {{{ t', RET t'; mlst_model t' dq (v :: vs) }}}.
  Proof.
    apply chain_cons_spec.
  Qed.
  Lemma mlst_singleton_spec v :
    {{{ True }}}
      mlst_singleton v
    {{{ t, RET t; mlst_model t (DfracOwn 1) [v] }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply mlst_cons_spec; [| iApply mlst_nil_spec |]; done.
  Qed.

  Lemma mlst_head_spec t dq v vs :
    {{{ mlst_model t dq (v :: vs) }}}
      mlst_head t
    {{{ RET v; mlst_model t dq (v :: vs) }}}.
  Proof.
    apply chain_head_spec.
  Qed.
  Lemma mlst_tail_spec t dq v vs :
    {{{ mlst_model t dq (v :: vs) }}}
      mlst_tail t
    {{{ t', RET t'; chain_model t dq [v] t' ∗ mlst_model t' dq vs }}}.
  Proof.
    apply chain_tail_spec.
  Qed.

  Lemma mlst_set_head_spec t v vs w :
    {{{ mlst_model t (DfracOwn 1) (v :: vs) }}}
      mlst_set_head t w
    {{{ RET #(); mlst_model t (DfracOwn 1) (w :: vs) }}}.
  Proof.
    apply chain_set_head_spec.
  Qed.
  Lemma mlst_set_tail_spec t v vs w :
    {{{ mlst_model t (DfracOwn 1) (v :: vs) }}}
      mlst_set_tail t w
    {{{ t',
      RET #();
      chain_model t (DfracOwn 1) [v] w ∗
      mlst_model t' (DfracOwn 1) vs
    }}}.
  Proof.
    apply chain_set_tail_spec.
  Qed.

  Lemma mlst_is_empty_spec t dq vs :
    {{{ mlst_model t dq vs }}}
      mlst_is_empty t
    {{{ RET #(bool_decide (vs = [])); mlst_model t dq vs }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec. wp_pures.
    destruct vs as [| v vs].
    - iDestruct (chain_model_nil_2 _ dq with "Hmodel") as %->.
      iApply "HΦ". iApply chain_model_nil_1.
    - iAssert ⌜t ≠ #()⌝%I as %?; last rewrite /= bool_decide_eq_false_2 //.
      { iDestruct (chain_model_app_2 [v] vs with "Hmodel") as "(%t' & Hmodel & _)"; first done.
        iSimpl in "Hmodel". iDestruct "Hmodel" as "(%l & %_ & -> & _)". done.
      }
      iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma mlst_advance_spec t dq vs (i : Z) :
    (0 ≤ i ≤ length vs)%Z →
    {{{ mlst_model t dq vs }}}
      mlst_advance t #i
    {{{ t',
      RET t';
      chain_model t dq (take (Z.to_nat i) vs) t' ∗
      mlst_model t' dq (drop (Z.to_nat i) vs)
    }}}.
  Proof.
    apply chain_advance_spec.
  Qed.

  Lemma mlst_get_spec t dq vs (i : Z) v :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{ mlst_model t dq vs }}}
      mlst_get t #i
    {{{ RET v; mlst_model t dq vs }}}.
  Proof.
    apply chain_get_spec.
  Qed.
  Lemma mlst_set_spec t vs (i : Z) v w :
    (0 ≤ i)%Z →
    vs !! Z.to_nat i = Some v →
    {{{ mlst_model t (DfracOwn 1) vs }}}
      mlst_set t #i w
    {{{ RET #(); mlst_model t (DfracOwn 1) (<[Z.to_nat i := w]> vs) }}}.
  Proof.
    apply chain_set_spec.
  Qed.

  (* Definition mlst_foldl : val := *)
  (*   rec: "mlst_foldl" "t" "acc" "fn" := *)
  (*     if: mlst_is_empty "t" then ( *)
  (*       "acc" *)
  (*     ) else ( *)
  (*       "mlst_foldl" (mlst_tail "t") ("fn" "acc" (mlst_head "t")) "fn" *)
  (*     ). *)

  (* Definition mlst_foldr : val := *)
  (*   rec: "mlst_foldr" "t" "fn" "acc" := *)
  (*     if: mlst_is_empty "t" then ( *)
  (*       "acc" *)
  (*     ) else ( *)
  (*       "fn" (mlst_head "t") ("mlst_foldr" (mlst_tail "t") "fn" "acc") *)
  (*     ). *)

  (* Definition mlst_size : val := *)
  (*   λ: "t", *)
  (*     mlst_foldl "t" #0 (λ: "acc" <>, "acc" + #1). *)

  (* Definition mlst_rev : val := *)
  (*   λ: "t", *)
  (*     mlst_foldl "t" mlst_nil (λ: "acc" "v", mlst_cons "v" "acc"). *)

  (* Definition mlst_copy : val := *)
  (*   λ: "t", *)
  (*     mlst_foldr "t" mlst_cons mlst_nil. *)

  (* Definition mlst_app : val := *)
  (*   λ: "t1" "t2", *)
  (*     mlst_foldr "t1" mlst_cons "t2". *)
  (* Definition mlst_snoc : val := *)
  (*   λ: "t" "v", *)
  (*     mlst_app "t" (mlst_singleton "v"). *)

  (* Definition mlst_iter : val := *)
  (*   λ: "t" "fn", *)
  (*     mlst_foldl "t" #() (λ: <> "v", "fn" "v"). *)

  (* Definition mlst_map : val := *)
  (*   rec: "lst_map" "t" "fn" := *)
  (*     if: mlst_is_empty "t" then ( *)
  (*       mlst_nil *)
  (*     ) else ( *)
  (*       let: "v" := "fn" "v" in *)
  (*       let: "t" := "mlst" "t" "fn" in *)
  (*       mlst_cons "v" "t" *)
  (*     ). *)
End heapGS.

#[global] Opaque mlst_nil.
#[global] Opaque mlst_cons.
#[global] Opaque mlst_singleton.
#[global] Opaque mlst_head.
#[global] Opaque mlst_tail.
#[global] Opaque mlst_set_head.
#[global] Opaque mlst_set_tail.
#[global] Opaque mlst_is_empty.
#[global] Opaque mlst_advance.
#[global] Opaque mlst_get.
#[global] Opaque mlst_set.
#[global] Opaque mlst_foldl.
#[global] Opaque mlst_foldr.
#[global] Opaque mlst_size.
#[global] Opaque mlst_rev.
#[global] Opaque mlst_copy.
#[global] Opaque mlst_app.
#[global] Opaque mlst_snoc.
#[global] Opaque mlst_iter.
#[global] Opaque mlst_map.

#[global] Typeclasses Opaque mlst_model.
